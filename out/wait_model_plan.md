Model plan for `ostd/src/sync/wait.rs`

Goal

Model `wait.rs` at the level needed by users such as `Mutex` and `RwMutex`, without trying to verify the full scheduler. The proof target should be:

- no lost wakeups relative to the intended usage pattern
- `wake_up` is one-shot for a live waiter
- dropping or cancelling a waiter makes future wakes no-ops
- `WaitQueue` preserves consistency between `num_wakers` and the queued entries

Non-goal

- proving scheduler fairness or eventual scheduling
- proving FIFO fairness across waiters
- modeling the internals of `Task` or `scheduler`

Core abstraction boundary

Treat these scheduler calls as trusted external actions with small specs:

- `scheduler::unpark_target(task)`:
  if the waiter is live and a wake is accepted, the task may become runnable
- `scheduler::park_current(pred)`:
  may return spuriously, but if `pred()` is true at entry it returns immediately

This keeps the proof in `wait.rs` focused on the wake protocol, not task scheduling.

1. Start with `Waker`, not `WaitQueue`

`Waker` is the real protocol object. `WaitQueue` is just a container of `Arc<Waker>`.

Use a ghost state machine for each `Waker`:

- `Idle`: live waiter, no pending wake
- `Signaled`: live waiter, one pending wake
- `Closed`: waiter is dropped or cancelled; future wakes do nothing

Important point: executable `has_woken: bool` cannot distinguish `Signaled` from `Closed`, so the ghost state must carry that distinction.

Suggested representation:

- keep `has_woken: AtomicBool<_, WakerGhost, _>`
- define `tracked struct WakerGhost { state: WakerState, task_token: Option<...> }`
- `enum WakerState { Idle, Signaled, Closed }`

Minimal invariant:

- `Idle <==> has_woken == false`
- `Signaled or Closed <==> has_woken == true`

The ghost part is what separates accepted wake from closed waiter.

2. Model the linear capability of a live waiter

You need one ghost resource that exists exactly while the waiter is live.

Use it to express:

- `Waiter::new_pair` creates one live waiter capability
- `close` consumes that capability or marks it closed
- `wake_up` can succeed only while the capability is still logically live

This can be done with a simple exclusive token stored in the `Waker` ghost state. Unlike the mutex case, here the token is useful because there are genuinely two ghost-distinct `has_woken == true` cases.

3. Specify `Waker::wake_up`

Desired spec:

- returns `true` only on transition `Idle -> Signaled`
- returns `false` on `Signaled` and `Closed`
- leaves the state as `Signaled` or `Closed` accordingly

Proof shape:

- atomic swap from `false` to `true`
- if old bit was `true`, return `false`
- if old bit was `false`, ghost state must have been `Idle`, so change it to `Signaled`
- then call trusted `unpark_target`

This is the core no-duplication property.

4. Specify `Waker::do_wait`

Do not try to prove scheduler progress. Instead prove the safety-style consumption rule:

- on entry, state is `Idle`, `Signaled`, or `Closed`
- if `Signaled`, `do_wait` consumes the pending wake and returns with state `Idle`
- if `Idle`, it may park repeatedly until some execution of `wake_up` changes the state to `Signaled`, then it consumes that signal and returns with state `Idle`
- if `Closed`, it should also return without creating a fresh wake

Operationally, `swap(false, Acquire)` acts as the signal-consumption point.

The proof should expose only this abstract postcondition:

- after `wait`, there is no pending wake left in the waker state

5. Specify `Waker::close`

This is the second place where the extra ghost state matters.

Desired transition:

- `Idle -> Closed`
- `Signaled -> Closed`
- `Closed -> Closed`

Executable code uses `swap(true, Acquire)`, so the atomic bit stays consistent.

The important spec consequence:

- after `close`, all future `wake_up` calls return `false`

6. Model `Waiter` as a thin owner of the live-waiter protocol

`Waiter` itself does not need much state beyond owning the associated `Arc<Waker>`.

Useful specs:

- `Waiter::new_pair` returns `(Waiter, Arc<Waker>)` attached to the same ghost waker state
- `wait()` forwards to `waker.do_wait()`
- `Drop for Waiter` calls `close()` and establishes the closed state

For `wait_until_or_cancelled`, keep the function mostly external-body if needed. The important spec is:

- returns `Ok(r)` only if `cond()` became `Some(r)`
- returns `Err(e)` only if cancellation fired and then the waker was closed before the final `cond()` re-check

7. Model `WaitQueue` as a bag/sequence of waker references

The queue must allow duplicate and stale entries.

This is important because `wait_until` enqueues the same `Waker` repeatedly across retries, and old entries can remain after a successful wake, cancellation, or drop. The implementation handles this by popping until `wake_up()` returns `true`.

So the ghost queue should be:

- a `Seq<WakerId>` if you want to preserve front-pop behavior
- or a multiset if you only care about count and existence

I recommend `Seq<WakerId>` because it matches the concrete `VecDeque` and makes `wake_one` / `wake_all` easier to explain.

Queue invariant:

- `num_wakers == queued_seq.len()`

Do not require queued entries to be live or unique.

8. Keep queue specs weak and compositional

For `enqueue(waker)`:

- append that waker id to the ghost sequence
- increment `num_wakers`

For `wake_one()`:

- if queue is empty, return `false`
- otherwise repeatedly pop from the front until either:
  - some popped waker accepts the wake, then return `true`
  - queue becomes empty, then return `false`
- in all cases, popped entries are removed from the ghost sequence and `num_wakers` stays equal to the remaining length

For `wake_all()`:

- clear the queue ghost sequence
- return the number of popped entries whose `wake_up()` succeeds

This is exactly the level needed by `Mutex::unlock` and the `RwMutex` wait paths.

9. Keep `wait_until` mostly abstract

`WaitQueue::wait_until` is harder than `wake_one` because it mixes:

- user condition
- queue insertion
- waiting
- retry loop

Do not try to fully verify arbitrary closures initially.

Recommended first step:

- keep `wait_until` as `external_body`
- document an abstract contract:
  - if `cond()` is already `Some(r)`, it returns `r`
  - otherwise it may enqueue its waiter and block/retry
  - if another thread first makes the condition true and then performs a wake on this queue, the waiter does not lose that wakeup

That contract is enough for `Mutex::lock` / `RwMutex::*lock`.

10. Suggested implementation order

1. Add a ghost state machine and invariant to `Waker`
2. Verify `wake_up`, `do_wait`, and `close`
3. Add a light type invariant to `Waiter`
4. Model `WaitQueue` with a ghost sequence mirroring `num_wakers`
5. Verify `enqueue`, `wake_one`, and `wake_all`
6. Leave `wait_until` and possibly `wait_until_or_cancelled` as abstract wrappers until the lower-level protocol is stable

11. What to expose to clients

Clients like `Mutex` should not depend on queue internals. Expose only:

- `wake_one` may make one waiter runnable if there is an effective queued wake target
- `wake_all` does the same for all queued entries
- `wait_until` does not lose wakeups when used in the documented order:
  producer makes condition true, then calls wake

12. Why this model is the right size

If you model only the `AtomicBool`, you cannot distinguish:

- already-signaled waiter
- closed waiter

and then `wake_up` / `close` specs become too weak. If you model the whole scheduler, the proof burden explodes for no gain. The right middle ground is:

- precise ghost protocol for `Waker`
- weak trusted scheduler interface
- queue as a ghost sequence of possibly stale waker references

That is enough to justify the uses in `mutex.rs` and `rwmutex.rs`.
