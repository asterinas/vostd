use vstd::prelude::*;
use vstd_extra::{state_machine::*, temporal_logic::*};

verus! {

pub type Tid = int;

#[derive(PartialEq, Eq, Clone, Copy)]
pub ghost enum Label {
    start,
    lock,
    unlock,
    cs,
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub ghost enum Procedure {
    acquire_lock,
    release_lock,
}

pub ghost struct StackFrame {
    pub procedure: Procedure,
    pub pc: Label,
}

pub ghost struct ProgramState {
    pub num_procs: nat,
    pub locked: bool,
    pub stack: Map<Tid, Seq<StackFrame>>,
    pub pc: Map<Tid, Label>,
}

pub open spec fn init(num_procs: nat) -> StatePred<ProgramState> {
    |s: ProgramState|
        {
            &&& s.num_procs == num_procs
            &&& s.locked == false
            &&& s.stack == Map::new(|i: Tid| 0 <= i < num_procs, |i| Seq::<StackFrame>::empty())
            &&& s.pc == Map::new(|i: Tid| 0 <= i < num_procs, |i| Label::start)
        }
}

pub open spec fn lock() -> Action<ProgramState, Tid, ()> {
    Action {
        precondition: |tid: Tid, s: ProgramState|
            {
                &&& 0 <= tid < s.num_procs
                &&& s.pc[tid] == Label::lock
                &&& s.locked == false
            },
        transition: |tid: Tid, s: ProgramState|
            {
                let s_prime = ProgramState {
                    locked: true,
                    pc: s.pc.insert(tid, s.stack[tid].first().pc),
                    stack: s.stack.insert(tid, s.stack[tid].drop_first()),
                    ..s
                };
                (s_prime, ())
            },
    }
}

pub open spec fn acquire_lock(tid: Tid) -> ActionPred<ProgramState> {
    lock().forward(tid)
}

pub open spec fn unlock() -> Action<ProgramState, Tid, ()> {
    Action {
        precondition: |tid: Tid, s: ProgramState|
            {
                &&& 0 <= tid < s.num_procs
                &&& s.pc[tid] == Label::unlock
            },
        transition: |tid: Tid, s: ProgramState|
            {
                let s_prime = ProgramState {
                    locked: false,
                    pc: s.pc.insert(tid, s.stack[tid].first().pc),
                    stack: s.stack.insert(tid, s.stack[tid].drop_first()),
                    ..s
                };
                (s_prime, ())
            },
    }
}

pub open spec fn release_lock(tid: Tid) -> ActionPred<ProgramState> {
    unlock().forward(tid)
}

pub open spec fn start() -> Action<ProgramState, Tid, ()> {
    Action {
        precondition: |tid: Tid, s: ProgramState|
            {
                &&& 0 <= tid < s.num_procs
                &&& s.pc[tid] == Label::start
            },
        transition: |tid: Tid, s: ProgramState|
            {
                let pre_stack = s.stack[tid];
                let frame = StackFrame { procedure: Procedure::acquire_lock, pc: Label::cs };
                let s_prime = ProgramState {
                    stack: s.stack.insert(
                        tid,
                        Seq::<StackFrame>::empty().push(frame).add(pre_stack),
                    ),
                    pc: s.pc.insert(tid, Label::lock),
                    ..s
                };
                (s_prime, ())
            },
    }
}

pub open spec fn cs() -> Action<ProgramState, Tid, ()> {
    Action {
        precondition: |tid: Tid, s: ProgramState|
            {
                &&& 0 <= tid < s.num_procs
                &&& s.pc[tid] == Label::cs
            },
        transition: |tid: Tid, s: ProgramState|
            {
                let pre_stack = s.stack[tid];
                let frame = StackFrame { procedure: Procedure::release_lock, pc: Label::start };
                let s_prime = ProgramState {
                    stack: s.stack.insert(
                        tid,
                        Seq::<StackFrame>::empty().push(frame).add(pre_stack),
                    ),
                    pc: s.pc.insert(tid, Label::unlock),
                    ..s
                };
                (s_prime, ())
            },
    }
}

pub open spec fn P(tid: Tid) -> ActionPred<ProgramState> {
    |s: ProgramState, s_prime: ProgramState|
        {
            ||| start().forward(tid)(s, s_prime)
            ||| cs().forward(tid)(s, s_prime)
        }
}

pub open spec fn next() -> ActionPred<ProgramState> {
    |s: ProgramState, s_prime: ProgramState|
        {
            exists|tid: Tid|
                0 <= tid < s.num_procs && {
                    ||| acquire_lock(tid)(s, s_prime)
                    ||| release_lock(tid)(s, s_prime)
                    ||| P(tid)(s, s_prime)
                }
        }
}

impl ProgramState {
    pub open spec fn valid_tid(self, tid: Tid) -> bool {
        0 <= tid < self.num_procs
    }

    pub open spec fn trying(self, tid: Tid) -> bool {
        self.pc[tid] == Label::lock
    }

    pub open spec fn mutual_exclusion(self) -> bool {
        forall|i: Tid, j: Tid|
            #![auto]
            (self.valid_tid(i) && self.valid_tid(j) && i != j) ==> !(self.pc[i] == Label::cs
                && self.pc[j] == Label::cs)
    }
}

pub open spec fn starvation_free() -> TempPred<ProgramState> {
    tla_forall(
        |i: Tid|
            lift_state(|s: ProgramState| s.valid_tid(i) && s.trying(i)).leads_to(
                lift_state(|s: ProgramState| s.pc[i] == Label::cs),
            ),
    )
}

pub open spec fn dead_and_alive_lock_free() -> TempPred<ProgramState> {
    tla_exists(
        |i: Tid|
            lift_state(|s: ProgramState| s.valid_tid(i) && s.trying(i)).leads_to(
                tla_exists(
                    |j: Tid| lift_state(|s: ProgramState| s.valid_tid(j) && s.pc[j] == Label::cs),
                ),
            ),
    )
}

pub open spec fn pc_stack_match(pc: Label, stack: Seq<StackFrame>) -> bool {
    match pc {
        Label::start => stack =~= Seq::empty(),
        Label::lock => stack =~= seq![
            StackFrame { procedure: Procedure::acquire_lock, pc: Label::cs },
        ],
        Label::cs => stack =~= Seq::empty(),
        Label::unlock => stack =~= seq![
            StackFrame { procedure: Procedure::release_lock, pc: Label::start },
        ],
    }
}

pub proof fn lemma_num_procs_unchanged(spec: TempPred<ProgramState>, n: nat)
    requires
        spec.entails(lift_state(init(n))),
        spec.entails(always(lift_action(next()))),
    ensures
        spec.entails(always(lift_state(|s: ProgramState| s.num_procs == n))),
{
    init_invariant(spec, init(n), next(), |s: ProgramState| { s.num_procs == n });
}

pub proof fn lemma_pc_stack_match(spec: TempPred<ProgramState>, n: nat)
    requires
        spec.entails(lift_state(init(n))),
        spec.entails(always(lift_action(next()))),
    ensures
        spec.entails(
            always(
                lift_state(
                    |s: ProgramState|
                        {
                            forall|tid: Tid| #[trigger]
                                s.valid_tid(tid) ==> pc_stack_match(s.pc[tid], s.stack[tid])
                        },
                ),
            ),
        ),
{
    lemma_num_procs_unchanged(spec, n);
    assert forall|s: ProgramState, s_prime: ProgramState|
        (forall|tid: Tid| #[trigger] s.valid_tid(tid) ==> pc_stack_match(s.pc[tid], s.stack[tid]))
            && #[trigger] next()(s, s_prime) implies (forall|tid: Tid| #[trigger]
        s_prime.valid_tid(tid) ==> pc_stack_match(s_prime.pc[tid], s_prime.stack[tid])) by {
        if (exists|tid: Tid| 0 <= tid < s.num_procs && acquire_lock(tid)(s, s_prime)) {
            let tid = choose|tid: Tid| 0 <= tid < s.num_procs && acquire_lock(tid)(s, s_prime);
            assert(s.valid_tid(tid));
            assert(s.pc[tid] == Label::lock);
            assert(s.stack[tid] == seq![
                StackFrame { procedure: Procedure::acquire_lock, pc: Label::cs },
            ]);
            assert(s_prime.pc[tid] == Label::cs);
            assert(s_prime.stack[tid] == Seq::<StackFrame>::empty());
            assert(pc_stack_match(s_prime.pc[tid], s_prime.stack[tid]));
            assert forall|tid0: Tid| #![auto] s_prime.valid_tid(tid0) implies pc_stack_match(
                s_prime.pc[tid0],
                s_prime.stack[tid0],
            ) by {
                if tid0 == tid {
                    // already proved above
                } else {
                    assert(s.valid_tid(tid0));
                    assert(s_prime.pc[tid0] == s.pc[tid0]);
                    assert(s_prime.stack[tid0] == s.stack[tid0]);
                    assert(pc_stack_match(s.pc[tid0], s.stack[tid0]));
                    assert(pc_stack_match(s_prime.pc[tid0], s_prime.stack[tid0]));
                }
            }
        }
        if (exists|tid: Tid| 0 <= tid < s.num_procs && release_lock(tid)(s, s_prime)) {
            if let tid = choose|tid: Tid| 0 <= tid < s.num_procs && release_lock(tid)(s, s_prime) {
                assert(s.valid_tid(tid));
                assert(s.pc[tid] == Label::unlock);
                assert(s.stack[tid] == seq![
                    StackFrame { procedure: Procedure::release_lock, pc: Label::start },
                ]);
                assert(s_prime.pc[tid] == Label::start);
                assert(s_prime.stack[tid] == Seq::<StackFrame>::empty());
                assert(pc_stack_match(s_prime.pc[tid], s_prime.stack[tid]));
                assert forall|tid0: Tid| #![auto] s_prime.valid_tid(tid0) implies pc_stack_match(
                    s_prime.pc[tid0],
                    s_prime.stack[tid0],
                ) by {
                    if tid0 == tid {
                        // already proved above
                    } else {
                        assert(s.valid_tid(tid0));
                        assert(s_prime.pc[tid0] == s.pc[tid0]);
                        assert(s_prime.stack[tid0] == s.stack[tid0]);
                        assert(pc_stack_match(s.pc[tid0], s.stack[tid0]));
                        assert(pc_stack_match(s_prime.pc[tid0], s_prime.stack[tid0]));
                    }
                }
            }
        }
        if (exists|tid: Tid| 0 <= tid < s.num_procs && P(tid)(s, s_prime)) {
            let tid = choose|tid: Tid| 0 <= tid < s.num_procs && P(tid)(s, s_prime);
            assert(s.valid_tid(tid));
            if (start().forward(tid)(s, s_prime)) {
                assert(s.pc[tid] == Label::start);
                assert(s.stack[tid] == Seq::<StackFrame>::empty());
                assert(s_prime.pc[tid] == Label::lock);
                assert(s_prime.stack[tid] == seq![
                    StackFrame { procedure: Procedure::acquire_lock, pc: Label::cs },
                ]);
                assert(pc_stack_match(s_prime.pc[tid], s_prime.stack[tid]));
            } else {
                assert(cs().forward(tid)(s, s_prime));
                assert(s.pc[tid] == Label::cs);
                assert(s.stack[tid] == Seq::<StackFrame>::empty());
                assert(s_prime.pc[tid] == Label::unlock);
                assert(s_prime.stack[tid] == seq![
                    StackFrame { procedure: Procedure::release_lock, pc: Label::start },
                ]);
                assert(pc_stack_match(s_prime.pc[tid], s_prime.stack[tid]));
            }
            assert forall|tid0: Tid| #![auto] s_prime.valid_tid(tid0) implies pc_stack_match(
                s_prime.pc[tid0],
                s_prime.stack[tid0],
            ) by {
                if tid0 == tid {
                    // already proved above
                } else {
                    assert(s.valid_tid(tid0));
                    assert(s_prime.pc[tid0] == s.pc[tid0]);
                    assert(s_prime.stack[tid0] == s.stack[tid0]);
                    assert(pc_stack_match(s.pc[tid0], s.stack[tid0]));
                    assert(pc_stack_match(s_prime.pc[tid0], s_prime.stack[tid0]));
                }
            }
        }
    }
    init_invariant(
        spec,
        init(n),
        next(),
        |s: ProgramState|
            { forall|tid: Tid| #![auto] s.valid_tid(tid) ==> pc_stack_match(s.pc[tid], s.stack[tid])
            },
    );
}

pub proof fn lemma_not_locked_iff_not_in_cs(spec: TempPred<ProgramState>, n: nat)
    requires
        spec.entails(lift_state(init(n))),
        spec.entails(always(lift_action(next()))),
    ensures
        spec.entails(
            always(
                lift_state(
                    |s: ProgramState|
                        {
                            !s.locked <==> forall|tid: Tid| #[trigger]
                                s.valid_tid(tid) ==> s.pc[tid] != Label::cs
                        },
                ),
            ),
        ),
{
    lemma_num_procs_unchanged(spec, n);
    lemma_pc_stack_match(spec, n);
    assert forall|s: ProgramState, s_prime: ProgramState|
        (!s.locked <==> forall|tid: Tid| #[trigger] s.valid_tid(tid) ==> s.pc[tid] != Label::cs)
            && #[trigger] next()(s, s_prime) implies (!s_prime.locked <==> forall |tid: Tid|
        #[trigger] s_prime.valid_tid(tid) ==> s_prime.pc[tid] != Label::cs) by {
        if (exists|tid: Tid| 0 <= tid < s.num_procs && acquire_lock(tid)(s, s_prime)) {
            let tid = choose|tid: Tid| 0 <= tid < s.num_procs && acquire_lock(tid)(s, s_prime);
            assert(s.valid_tid(tid));
            assert(s.pc[tid] == Label::lock);
            assert(pc_stack_match(s.pc[tid], s.stack[tid])) by {admit();};
            assert(s.stack[tid] == seq![
                StackFrame { procedure: Procedure::acquire_lock, pc: Label::cs },
            ]);
            assert(s_prime.locked == true);
            assert(s_prime.valid_tid(tid));
            assert(s_prime.pc[tid] == Label::cs);
            assert (!s_prime.locked <==> forall|tid0: Tid| #[trigger] s_prime.valid_tid(tid0) ==> s_prime.pc[tid0] != Label::cs); 
        }
        if (exists|tid: Tid| 0 <= tid < s.num_procs && release_lock(tid)(s, s_prime)) {
            admit();
        }
        if (exists|tid: Tid| 0 <= tid < s.num_procs && P(tid)(s, s_prime)) {
            admit();
        }
        init_invariant(
            spec,
            init(n),
            next(),
            |s: ProgramState|
                {
                    !s.locked ==> forall|tid: Tid| #[trigger]
                        s.valid_tid(tid) ==> s.pc[tid] != Label::cs
                },
        );
    }
}

pub proof fn lemma_mutual_exclusion(spec: TempPred<ProgramState>, n: nat)
    requires
        spec.entails(lift_state(init(n))),
        spec.entails(always(lift_action(next()))),
    ensures
        spec.entails(always(lift_state(|s: ProgramState| s.mutual_exclusion()))),
{
    lemma_num_procs_unchanged(spec, n);
    lemma_pc_stack_match(spec, n);
    /*assert forall|s: ProgramState, s_prime: ProgramState|
        s.mutual_exclusion() && #[trigger] next()(
            s,
            s_prime,
        ) implies s_prime.mutual_exclusion() by {
        if (exists|tid: Tid| 0 <= tid < s.num_procs && acquire_lock(tid)(s, s_prime)) {
            assert(s.mutual_exclusion());
            let tid = choose|tid: Tid| 0 <= tid < s.num_procs && acquire_lock(tid)(s, s_prime);
            assert(s.pc[tid] == Label::lock);
            admit();
        }
        if (exists|tid: Tid| 0 <= tid < s.num_procs && release_lock(tid)(s, s_prime)) {
            admit();
        }
        if (exists|tid: Tid| 0 <= tid < s.num_procs && P(tid)(s, s_prime)) {
            admit();
        }
    }*/

    init_invariant(spec, init(n), next(), |s: ProgramState| { s.mutual_exclusion() });
}

} // verus!
