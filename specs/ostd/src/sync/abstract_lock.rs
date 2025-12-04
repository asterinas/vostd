use vstd::pervasive::trigger;
use vstd::prelude::*;
use vstd::set_lib::*;
use vstd_extra::{set_extra::*, state_machine::*, temporal_logic::*};

use super::mutex::pre_check_lock;

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
    pub ProcSet: Set<Tid>,
    pub locked: bool,
    pub stack: Map<Tid, Seq<StackFrame>>,
    pub pc: Map<Tid, Label>,
}

pub open spec fn init(num_procs: nat) -> StatePred<ProgramState> {
    |s: ProgramState|
        {
            &&& s.ProcSet == set_int_range(0, num_procs as int)
            &&& s.locked == false
            &&& s.stack == s.ProcSet.mk_map(|i: Tid| Seq::<StackFrame>::empty())
            &&& s.pc == s.ProcSet.mk_map(|i: Tid| Label::start)
        }
}

pub open spec fn lock() -> Action<ProgramState, Tid, ()> {
    Action {
        precondition: |tid: Tid, s: ProgramState|
            {
                &&& s.in_ProcSet(tid)
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
                &&& s.in_ProcSet(tid)
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
                &&& s.in_ProcSet(tid)
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
                &&& s.in_ProcSet(tid)
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
            exists|tid: Tid| #[trigger]
                s.in_ProcSet(tid) && {
                    ||| acquire_lock(tid)(s, s_prime)
                    ||| release_lock(tid)(s, s_prime)
                    ||| P(tid)(s, s_prime)
                }
        }
}

pub proof fn lemma_next_keeps_invariant_decouple(inv: StatePred<ProgramState>)
    requires
        forall|s: ProgramState, s_prime: ProgramState, tid: Tid|
            s.in_ProcSet(tid) && inv(s) && #[trigger] acquire_lock(tid)(s, s_prime) ==> inv(
                s_prime,
            ),
        forall|s: ProgramState, s_prime: ProgramState, tid: Tid|
            s.in_ProcSet(tid) && inv(s) && #[trigger] release_lock(tid)(s, s_prime) ==> inv(
                s_prime,
            ),
        forall|s: ProgramState, s_prime: ProgramState, tid: Tid|
            s.in_ProcSet(tid) && inv(s) && #[trigger] start().forward(tid)(s, s_prime) ==> inv(
                s_prime,
            ),
        forall|s: ProgramState, s_prime: ProgramState, tid: Tid|
            s.in_ProcSet(tid) && inv(s) && #[trigger] cs().forward(tid)(s, s_prime) ==> inv(
                s_prime,
            ),
    ensures
        forall|s: ProgramState, s_prime: ProgramState|
            inv(s) && #[trigger] next()(s, s_prime) ==> inv(s_prime),
{
}

impl ProgramState {
    pub open spec fn in_ProcSet(self, tid: Tid) -> bool {
        self.ProcSet.contains(tid)
    }

    pub open spec fn trying(self, tid: Tid) -> bool {
        self.pc[tid] == Label::lock
    }

    pub open spec fn mutual_exclusion(self) -> bool {
        forall|i: Tid, j: Tid|
            (#[trigger] self.in_ProcSet(i) && #[trigger] self.in_ProcSet(j) && i != j) ==> !(
            self.pc[i] == Label::cs && self.pc[j] == Label::cs)
    }

    pub open spec fn inv_unchanged(self, n: nat) -> bool {
        &&& self.ProcSet == set_int_range(0, n as int)
        &&& self.ProcSet.finite()
        &&& self.pc.dom() == self.ProcSet
        &&& self.stack.dom() == self.ProcSet
    }

    pub open spec fn inv_not_locked_iff_no_cs(self) -> bool {
        (!self.locked <==> self.ProcSet.filter(
            |tid: Tid| self.pc[tid] == Label::cs || self.pc[tid] == Label::unlock,
        ).is_empty()) && (self.locked <==> self.ProcSet.filter(
            |tid: Tid| self.pc[tid] == Label::cs || self.pc[tid] == Label::unlock,
        ).is_singleton())
    }

    pub open spec fn inv_pc_stack_match(self) -> bool {
        self.ProcSet.all(|tid: Tid| pc_stack_match(self.pc[tid], self.stack[tid]))
    }
}

pub open spec fn starvation_free() -> TempPred<ProgramState> {
    tla_forall(
        |i: Tid|
            lift_state(|s: ProgramState| s.in_ProcSet(i) && s.trying(i)).leads_to(
                lift_state(|s: ProgramState| s.pc[i] == Label::cs),
            ),
    )
}

pub open spec fn dead_and_alive_lock_free() -> TempPred<ProgramState> {
    lift_state_exists(|i: Tid| |s: ProgramState| s.in_ProcSet(i) && s.trying(i)).leads_to(
        lift_state_exists(|j: Tid| |s: ProgramState| s.in_ProcSet(j) && s.pc[j] == Label::cs),
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

pub proof fn lemma_inv_unchanged(spec: TempPred<ProgramState>, n: nat)
    requires
        spec.entails(lift_state(init(n))),
        spec.entails(always(lift_action(next()))),
    ensures
        spec.entails(always(lift_state(|s: ProgramState| s.inv_unchanged(n)))),
{
    lemma_int_range(0, n as int);
    assert forall|s: ProgramState, s_prime: ProgramState, tid: Tid|
        s.inv_unchanged(n) && s.in_ProcSet(tid) && #[trigger] acquire_lock(tid)(
            s,
            s_prime,
        ) implies s_prime.inv_unchanged(n) by {
        assert(s.pc.dom() == s_prime.pc.dom());
    }
    assert forall|s: ProgramState, s_prime: ProgramState, tid: Tid|
        s.inv_unchanged(n) && s.in_ProcSet(tid) && #[trigger] release_lock(tid)(
            s,
            s_prime,
        ) implies s_prime.inv_unchanged(n) by {
        assert(s.pc.dom() == s_prime.pc.dom());
    }
    assert forall|s: ProgramState, s_prime: ProgramState, tid: Tid|
        s.inv_unchanged(n) && s.in_ProcSet(tid) && #[trigger] start().forward(tid)(
            s,
            s_prime,
        ) implies s_prime.inv_unchanged(n) by {
        assert(s.pc.dom() == s_prime.pc.dom());
    }
    assert forall|s: ProgramState, s_prime: ProgramState, tid: Tid|
        s.inv_unchanged(n) && s.in_ProcSet(tid) && #[trigger] cs().forward(tid)(
            s,
            s_prime,
        ) implies s_prime.inv_unchanged(n) by {
        assert(s.pc.dom() == s_prime.pc.dom());
    }
    lemma_next_keeps_invariant_decouple(|s: ProgramState| { s.inv_unchanged(n) });
    init_invariant(spec, init(n), next(), |s: ProgramState| { s.inv_unchanged(n) });
}

pub proof fn lemma_inv_pc_stack_match(spec: TempPred<ProgramState>, n: nat)
    requires
        spec.entails(lift_state(init(n))),
        spec.entails(always(lift_action(next()))),
    ensures
        spec.entails(always(lift_state(|s: ProgramState| s.inv_pc_stack_match()))),
{
    lemma_inv_unchanged(spec, n);
    init_invariant(spec, init(n), next(), |s: ProgramState| { s.inv_pc_stack_match() });
}

pub proof fn lemma_not_locked_iff_not_in_cs(spec: TempPred<ProgramState>, n: nat)
    requires
        spec.entails(lift_state(init(n))),
        spec.entails(always(lift_action(next()))),
    ensures
        spec.entails(always(lift_state(|s: ProgramState| s.inv_not_locked_iff_no_cs()))),
{
    broadcast use group_tla_rules;

    lemma_inv_unchanged(spec, n);
    lemma_inv_pc_stack_match(spec, n);
    let inv_unchanged_state_pred = |s: ProgramState| s.inv_unchanged(n);
    let pc_stack_match_state_pred = |s: ProgramState| s.inv_pc_stack_match();
    let inv_not_locked_iff_no_cs_closure = |s: ProgramState| s.inv_not_locked_iff_no_cs();
    assert forall|s: ProgramState, s_prime: ProgramState, tid: Tid| #[trigger]
        acquire_lock(tid)(s, s_prime) && s.inv_unchanged(n) && pc_stack_match_state_pred(s)
            && s.inv_not_locked_iff_no_cs() implies s_prime.inv_not_locked_iff_no_cs() by {
        assert(s_prime.ProcSet.filter(
            |tid: Tid| s_prime.pc[tid] == Label::cs || s_prime.pc[tid] == Label::unlock,
        ) == s.ProcSet.filter(
            |tid: Tid| s.pc[tid] == Label::cs || s.pc[tid] == Label::unlock,
        ).insert(tid)) by {};
    };
    assert forall|s: ProgramState, s_prime: ProgramState, tid: Tid| #[trigger]
        release_lock(tid)(s, s_prime) && s.inv_unchanged(n) && pc_stack_match_state_pred(s)
            && s.inv_not_locked_iff_no_cs() implies s_prime.inv_not_locked_iff_no_cs() by {
        assert(s_prime.ProcSet.filter(
            |tid: Tid| s_prime.pc[tid] == Label::cs || s_prime.pc[tid] == Label::unlock,
        ) == s.ProcSet.filter(
            |tid: Tid| s.pc[tid] == Label::cs || s.pc[tid] == Label::unlock,
        ).remove(tid)) by {};
    };
    assert forall|s: ProgramState, s_prime: ProgramState, tid: Tid| #[trigger]
        start().forward(tid)(s, s_prime) && s.inv_unchanged(n) && pc_stack_match_state_pred(s)
            && s.inv_not_locked_iff_no_cs() implies s_prime.inv_not_locked_iff_no_cs() by {
        assert(s_prime.ProcSet.filter(
            |tid: Tid| s_prime.pc[tid] == Label::cs || s_prime.pc[tid] == Label::unlock,
        ) == s.ProcSet.filter(|tid: Tid| s.pc[tid] == Label::cs || s.pc[tid] == Label::unlock))
            by {};
    };
    assert forall|s: ProgramState, s_prime: ProgramState, tid: Tid| #[trigger]
        cs().forward(tid)(s, s_prime) && s.inv_unchanged(n) && pc_stack_match_state_pred(s)
            && s.inv_not_locked_iff_no_cs() implies s_prime.inv_not_locked_iff_no_cs() by {
        assert(s_prime.ProcSet.filter(
            |tid: Tid| s_prime.pc[tid] == Label::cs || s_prime.pc[tid] == Label::unlock,
        ) == s.ProcSet.filter(
            |tid: Tid| s.pc[tid] == Label::cs || s.pc[tid] == Label::unlock,
        ).insert(tid)) by {};
    };

    assert(forall|s: ProgramState, s_prime: ProgramState| #[trigger]
        next()(s, s_prime) && s.inv_unchanged(n) && pc_stack_match_state_pred(s)
            && s.inv_not_locked_iff_no_cs() ==> s_prime.inv_not_locked_iff_no_cs());
    strengthen_invariant_n!(spec, init(n), next(), inv_not_locked_iff_no_cs_closure, inv_unchanged_state_pred, pc_stack_match_state_pred);
}

pub proof fn lemma_mutual_exclusion(spec: TempPred<ProgramState>, n: nat)
    requires
        spec.entails(lift_state(init(n))),
        spec.entails(always(lift_action(next()))),
    ensures
        spec.entails(always(lift_state(|s: ProgramState| s.mutual_exclusion()))),
{
    broadcast use group_tla_rules;

    lemma_inv_unchanged(spec, n);
    lemma_not_locked_iff_not_in_cs(spec, n);
    let inv_unchanged_state_pred = |s: ProgramState| s.inv_unchanged(n);
    let inv_not_locked_iff_no_cs_closure = |s: ProgramState| s.inv_not_locked_iff_no_cs();
    let mutual_exclusion_closure = |s: ProgramState| s.mutual_exclusion();
    assert forall|s: ProgramState|
        s.inv_unchanged(n)
            && s.inv_not_locked_iff_no_cs() implies #[trigger] s.mutual_exclusion() by {
        lemma_set_prop_mutual_exclusion(s.ProcSet, |tid: Tid| s.pc[tid] == Label::cs);
        assert(s.ProcSet.filter(|tid: Tid| s.pc[tid] == Label::cs).len() <= 1) by {
            Set::lemma_is_singleton(
                s.ProcSet.filter(|tid: Tid| s.pc[tid] == Label::cs || s.pc[tid] == Label::unlock),
            );
            lemma_len_subset(
                s.ProcSet.filter(|tid: Tid| s.pc[tid] == Label::cs),
                s.ProcSet.filter(|tid: Tid| s.pc[tid] == Label::cs || s.pc[tid] == Label::unlock),
            );
        }
    };
    always_lift_state_weaken_n!(
        spec,
        inv_not_locked_iff_no_cs_closure,
        inv_unchanged_state_pred,
        mutual_exclusion_closure,
    );
}

pub proof fn lemma_pc_stack_match_statdead_and_alive_lock_freee_pred_case_not_locked(
    spec: TempPred<ProgramState>,
    n: nat,
)
    requires
        spec.entails(lift_state(init(n))),
        spec.entails(always(lift_action(next()))),
        spec.entails(tla_forall(|tid| weak_fairness(acquire_lock(tid)))),
        spec.entails(tla_forall(|tid| weak_fairness(release_lock(tid)))),
        spec.entails(tla_forall(|tid| weak_fairness(P(tid)))),
    ensures
        spec.entails(
            lift_state_exists(
                |i: Tid| |s: ProgramState| s.in_ProcSet(i) && s.trying(i) && !s.locked,
            ).leads_to(
                lift_state_exists(
                    |j: Tid| |s: ProgramState| s.in_ProcSet(j) && s.pc[j] == Label::cs,
                ),
            ),
        ),
{
    broadcast use group_tla_rules;

    let pre_state_pred = |tid: Tid|
        |s: ProgramState| s.in_ProcSet(tid) && s.trying(tid) && !s.locked;
    let post_state_pred = |tid: Tid| |s: ProgramState| s.in_ProcSet(tid) && s.pc[tid] == Label::cs;

    let inv_unchanged_state_pred = |s: ProgramState| s.inv_unchanged(n);
    let pc_stack_match_state_pred = |s: ProgramState| s.inv_pc_stack_match();
    let inv_not_locked_iff_no_cs_closure = |s: ProgramState| s.inv_not_locked_iff_no_cs();
    lemma_not_locked_iff_not_in_cs(spec, n);
    lemma_inv_pc_stack_match(spec, n);
    lemma_inv_unchanged(spec, n);

    assert forall|tid|
        spec.entails(
            (#[trigger] lift_state(pre_state_pred(tid))).leads_to(
                lift_state_exists(
                    |tid| |s: ProgramState| s.in_ProcSet(tid) && s.pc[tid] == Label::cs,
                ),
            ),
        ) by {
        assert forall|s: ProgramState, s_prime: ProgramState|
            s.in_ProcSet(tid) && s.trying(tid) && !s.locked && s.inv_not_locked_iff_no_cs()
                && s.inv_pc_stack_match() && s.inv_unchanged(n) && #[trigger] next()(
                s,
                s_prime,
            ) implies s_prime.in_ProcSet(tid) && s_prime.trying(tid) && !s_prime.locked
            || state_exists(post_state_pred)(s_prime) by {
            if (exists|tid0| #[trigger] s.in_ProcSet(tid0) && acquire_lock(tid0)(s, s_prime)) {
                let tid0 = choose|tid0| #[trigger]
                    s.in_ProcSet(tid0) && acquire_lock(tid0)(s, s_prime);
                assert(s_prime.in_ProcSet(tid0) && s_prime.pc[tid0] == Label::cs);
                // This proof is to enable the trigger on state_exists in the conclusion
                assert(exists|tid| #[trigger]
                    s_prime.in_ProcSet(tid) && post_state_pred(tid)(s_prime));
            }
        };
        assert(spec.entails(weak_fairness(acquire_lock(tid)))) by {
            use_tla_forall(spec, |tid| weak_fairness(acquire_lock(tid)), tid);
        }
        assert forall|s: ProgramState| #[trigger]
            s.in_ProcSet(tid) && s.trying(tid) && !s.locked && s.inv_not_locked_iff_no_cs()
                && s.inv_pc_stack_match() && s.inv_unchanged(n) implies enabled(acquire_lock(tid))(
            s,
        ) by {
            lock().lemma_statisfy_pre_implies_enabled(tid, s);
        };

        wf1_with_inv_n!(
            spec,
            next(),
            acquire_lock(tid),
            pre_state_pred(tid),
            state_exists(post_state_pred),
            inv_unchanged_state_pred,
            inv_not_locked_iff_no_cs_closure,
            pc_stack_match_state_pred,
        );
    };
}

pub proof fn lemma_pc_stack_match_statdead_and_alive_lock_freee_pred_case_locked(
    spec: TempPred<ProgramState>,
    n: nat,
)
    requires
        spec.entails(lift_state(init(n))),
        spec.entails(always(lift_action(next()))),
        spec.entails(tla_forall(|tid| weak_fairness(acquire_lock(tid)))),
        spec.entails(tla_forall(|tid| weak_fairness(release_lock(tid)))),
        spec.entails(tla_forall(|tid| weak_fairness(P(tid)))),
    ensures
        spec.entails(
            lift_state_exists(
                |i: Tid| |s: ProgramState| s.in_ProcSet(i) && s.trying(i) && s.locked,
            ).leads_to(
                lift_state_exists(
                    |i: Tid| |s: ProgramState| s.in_ProcSet(i) && s.trying(i) && !s.locked,
                ),
            ),
        ),
{
    broadcast use group_tla_rules;

    let pre_fn = |i: Tid| |s: ProgramState| s.in_ProcSet(i) && s.trying(i) && s.locked;
    let post_fn = |i: Tid| |s: ProgramState| s.in_ProcSet(i) && s.trying(i) && !s.locked;
    let post = lift_state_exists(post_fn);

    let inv_unchanged_state_pred = |s: ProgramState| s.inv_unchanged(n);
    let pc_stack_match_state_pred = |s: ProgramState| s.inv_pc_stack_match();
    let inv_not_locked_iff_no_cs_closure = |s: ProgramState| s.inv_not_locked_iff_no_cs();
    lemma_not_locked_iff_not_in_cs(spec, n);
    lemma_inv_pc_stack_match(spec, n);
    lemma_inv_unchanged(spec, n);

    assert forall|i: Tid| #[trigger] spec.entails(lift_state(pre_fn(i)).leads_to(post)) by {
        let pre_i_j = |j: Tid|
            |s: ProgramState|
                s.in_ProcSet(i) && s.trying(i) && s.in_ProcSet(j) && (s.pc[j] == Label::cs
                    || s.pc[j] == Label::unlock);

        assert forall|s: ProgramState| pre_fn(i)(s) && s.inv_not_locked_iff_no_cs() implies exists|
            j: Tid,
        | #[trigger]
            pre_i_j(j)(s) by {
            if pre_fn(i)(s) && s.inv_not_locked_iff_no_cs() {
                // locked implies exists j. pc[j] == cs || pc[j] == unlock
                // inv_not_locked_iff_no_cs says: locked <==> filter(...).is_singleton()
                // So filter(...) is not empty.
                let set = s.ProcSet.filter(
                    |tid: Tid| s.pc[tid] == Label::cs || s.pc[tid] == Label::unlock,
                );
                let j = set.choose();
                assert(set.contains(j));
                assert(pre_i_j(j)(s));
            }
        };

        assert forall|j: Tid| #[trigger] spec.entails(lift_state(pre_i_j(j)).leads_to(post)) by {
            let cond_cs = |s: ProgramState|
                s.in_ProcSet(i) && s.trying(i) && s.in_ProcSet(j) && s.pc[j] == Label::cs;
            let cond_unlock = |s: ProgramState|
                s.in_ProcSet(i) && s.trying(i) && s.in_ProcSet(j) && s.pc[j] == Label::unlock;

            // Step 1: cond_cs ~> cond_unlock
            assert(spec.entails(lift_state(cond_cs).leads_to(lift_state(cond_unlock)))) by {
                assert(spec.entails(weak_fairness(P(j)))) by {
                    use_tla_forall(spec, |tid| weak_fairness(P(tid)), j);
                }

                let inv = |s: ProgramState|
                    s.inv_unchanged(n) && s.inv_not_locked_iff_no_cs() && s.inv_pc_stack_match();

                assert forall|s: ProgramState| #[trigger] cond_cs(s) && inv(s) implies enabled(
                    P(j),
                )(s) by {
                    assert((cs().precondition)(j, s));
                    let (s_prime, _) = (cs().transition)(j, s);
                    assert(P(j)(s, s_prime));
                };

                assert forall|s, s_prime|
                    cond_cs(s) && inv(s) && #[trigger] next()(s, s_prime) implies cond_cs(s_prime)
                    || cond_unlock(s_prime) by {
                    if exists|tid| #[trigger] s.in_ProcSet(tid) && acquire_lock(tid)(s, s_prime) {
                        // Impossible because locked
                        let tid = choose|tid| #[trigger]
                            s.in_ProcSet(tid) && acquire_lock(tid)(s, s_prime);
                        assert(s.pc[j] == Label::cs);
                        let set = s.ProcSet.filter(
                            |tid: Tid| s.pc[tid] == Label::cs || s.pc[tid] == Label::unlock,
                        );
                        assert(set.contains(j));
                        assert(!set.is_empty());
                        assert(s.locked);
                        assert(false);
                    }
                };

                wf1_with_inv_n!(
                    spec,
                    next(),
                    P(j),
                    cond_cs,
                    cond_unlock,
                    inv_unchanged_state_pred,
                    inv_not_locked_iff_no_cs_closure,
                    pc_stack_match_state_pred,
                );
            };

            // Step 2: cond_unlock ~> post
            assert(spec.entails(lift_state(cond_unlock).leads_to(post))) by {
                let inv = |s: ProgramState|
                    s.inv_unchanged(n) && s.inv_not_locked_iff_no_cs() && s.inv_pc_stack_match();

                assert(spec.entails(weak_fairness(release_lock(j)))) by {
                    use_tla_forall(spec, |tid| weak_fairness(release_lock(tid)), j);
                }

                assert forall|s: ProgramState| #[trigger] cond_unlock(s) && inv(s) implies enabled(
                    release_lock(j),
                )(s) by {
                    assert((unlock().precondition)(j, s));
                    let (s_prime, _) = (unlock().transition)(j, s);
                    assert(release_lock(j)(s, s_prime));
                };

                assert forall|s, s_prime|
                    cond_unlock(s) && inv(s) && #[trigger] next()(s, s_prime) implies cond_unlock(
                    s_prime,
                ) || post_fn(i)(s_prime) by {
                    if exists|tid| #[trigger] s.in_ProcSet(tid) && acquire_lock(tid)(s, s_prime) {
                        // Impossible because locked
                        assert(s.pc[j] == Label::unlock);
                        let set = s.ProcSet.filter(
                            |tid: Tid| s.pc[tid] == Label::cs || s.pc[tid] == Label::unlock,
                        );
                        assert(set.contains(j));
                        assert(!set.is_empty());
                        assert(s.locked);
                        assert(false);
                    }
                };

                wf1_with_inv_n!(
                    spec,
                    next(),
                    release_lock(j),
                    cond_unlock,
                    post_fn(i),
                    inv_unchanged_state_pred,
                    inv_not_locked_iff_no_cs_closure,
                    pc_stack_match_state_pred,
                );

                lift_state_exists_equality(post_fn);
                leads_to_weaken(
                    spec,
                    lift_state(cond_unlock),
                    lift_state(post_fn(i)),
                    lift_state(cond_unlock),
                    post,
                );
            };

            leads_to_trans(spec, lift_state(cond_cs), lift_state(cond_unlock), post);

            or_leads_to_combine(spec, lift_state(cond_cs), lift_state(cond_unlock), post);
            temp_pred_equality(
                lift_state(pre_i_j(j)),
                lift_state(cond_cs).or(lift_state(cond_unlock)),
            );
            assert(spec.entails(lift_state(pre_i_j(j)).leads_to(post)));
        };

        lift_state_exists_leads_to_intro(spec, pre_i_j, post);
        // Now we have lift_state_exists(pre_i_j) ~> post

        // pre_fn(i) implies lift_state_exists(pre_i_j) (under invariant)
        // So lift_state(pre_fn(i)) ~> post
        assert(spec.entails(lift_state(pre_fn(i)).leads_to(lift_state_exists(pre_i_j)))) by {
            let inv = |s: ProgramState|
                s.inv_unchanged(n) && s.inv_not_locked_iff_no_cs() && s.inv_pc_stack_match();
            lift_state_exists_equality(pre_i_j);
            let exists_pred = |s: ProgramState| exists|j: Tid| #[trigger] pre_i_j(j)(s);
            // lift_state_exists(pre_i_j) == lift_state(exists_pred)

            assert forall|s| #[trigger] pre_fn(i)(s) && inv(s) implies exists_pred(s) by {
                if pre_fn(i)(s) && inv(s) {
                    let set = s.ProcSet.filter(
                        |tid: Tid| s.pc[tid] == Label::cs || s.pc[tid] == Label::unlock,
                    );
                    let j = set.choose();
                    assert(pre_i_j(j)(s));
                }
            };

            // spec entails always(inv)
            let combined = |s: ProgramState|
                inv_unchanged_state_pred(s) && inv_not_locked_iff_no_cs_closure(s)
                    && pc_stack_match_state_pred(s);
            entails_always_lift_state_and_n!(
                 spec,
                 inv_unchanged_state_pred,
                 inv_not_locked_iff_no_cs_closure,
                 pc_stack_match_state_pred
             );
            assert(spec.entails(always(lift_state(inv)))) by {
                assert forall|s| #[trigger] inv(s) == combined(s) by {};
                assert(lift_state(inv) == lift_state(combined));
            };

            // so spec entails always(pre_fn(i) implies exists_pred)
            assert(spec.entails(always(lift_state(pre_fn(i)).implies(lift_state(exists_pred)))))
                by {
                assert(lift_state(inv).entails(
                    lift_state(pre_fn(i)).implies(lift_state(exists_pred)),
                ));
                entails_preserved_by_always(
                    lift_state(inv),
                    lift_state(pre_fn(i)).implies(lift_state(exists_pred)),
                );
                entails_trans(
                    spec,
                    always(lift_state(inv)),
                    always(lift_state(pre_fn(i)).implies(lift_state(exists_pred))),
                );
            };
            always_implies_to_leads_to(spec, lift_state(pre_fn(i)), lift_state(exists_pred));
        };

        leads_to_trans(spec, lift_state(pre_fn(i)), lift_state_exists(pre_i_j), post);
    };

    lift_state_exists_leads_to_intro(spec, pre_fn, post);
}

pub proof fn lemma_pc_stack_match_statdead_and_alive_lock_freee_pred(
    spec: TempPred<ProgramState>,
    n: nat,
)
    requires
        spec.entails(lift_state(init(n))),
        spec.entails(always(lift_action(next()))),
        spec.entails(tla_forall(|tid| weak_fairness(acquire_lock(tid)))),
        spec.entails(tla_forall(|tid| weak_fairness(release_lock(tid)))),
        spec.entails(tla_forall(|tid| weak_fairness(P(tid)))),
    ensures
        spec.entails(dead_and_alive_lock_free()),
{
    broadcast use group_tla_rules;

    admit();
}

pub proof fn lemma_starvation_free(spec: TempPred<ProgramState>, n: nat)
    requires
        spec.entails(lift_state(init(n))),
        spec.entails(always(lift_action(next()))),
        spec.entails(tla_forall(|tid| weak_fairness(acquire_lock(tid)))),
        spec.entails(tla_forall(|tid| weak_fairness(release_lock(tid)))),
        spec.entails(tla_forall(|tid| weak_fairness(P(tid)))),
    ensures
        spec.entails(starvation_free()),
{
    admit();
}

} // verus!
