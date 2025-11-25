use vstd::prelude::*;
use vstd::set_lib::*;
use vstd_extra::{set_extra::*,state_machine::*, temporal_logic::*};

verus! {

pub open spec fn bool_implies(p: bool, q: bool) -> bool {
    (!p) || q
}

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
            exists|tid: Tid|
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
            #![auto]
            (self.in_ProcSet(i) && self.in_ProcSet(j) && i != j) ==> !(self.pc[i] == Label::cs
                && self.pc[j] == Label::cs)
    }

    pub open spec fn inv_unchanged(self, n: nat) -> bool {
        &&& self.ProcSet == set_int_range(0, n as int)
        &&& self.ProcSet.finite()
        &&& self.pc.dom() == self.ProcSet
        &&& self.stack.dom() == self.ProcSet
    }

    pub open spec fn holds_lock(self, tid: Tid) -> bool {
        self.pc[tid] == Label::cs || self.pc[tid] == Label::unlock
    }

    pub open spec fn not_locked_iff_no_cs(self) -> bool {
        if self.locked {
            exists|owner: Tid|
                self.in_ProcSet(owner)
                    && self.holds_lock(owner)
                    && forall|tid: Tid|
                        self.in_ProcSet(tid) && self.holds_lock(tid) ==> tid == owner
        } else {
            forall|tid: Tid| self.in_ProcSet(tid) ==> !self.holds_lock(tid)
        }
    }
}

pub proof fn lemma_unlocked_means_no_holders(s: ProgramState)
    requires
        !s.locked,
        s.not_locked_iff_no_cs(),
    ensures
        forall|tid: Tid| s.in_ProcSet(tid) ==> !s.holds_lock(tid),
{
    assert(forall|tid: Tid| s.in_ProcSet(tid) ==> !s.holds_lock(tid));
}

pub proof fn lemma_locked_unique_holder(s: ProgramState) -> (owner: Tid)
    requires
        s.locked,
        s.not_locked_iff_no_cs(),
    ensures
        s.in_ProcSet(owner),
        s.holds_lock(owner),
        forall|tid: Tid| s.in_ProcSet(tid) && s.holds_lock(tid) ==> tid == owner,
{
    assert(exists|candidate: Tid|
        s.in_ProcSet(candidate) && s.holds_lock(candidate) && forall|tid: Tid|
            s.in_ProcSet(tid) && s.holds_lock(tid) ==> tid == candidate);
    let owner = choose|candidate: Tid|
        s.in_ProcSet(candidate) && s.holds_lock(candidate) && forall|tid: Tid|
            s.in_ProcSet(tid) && s.holds_lock(tid) ==> tid == candidate;
    assert(s.in_ProcSet(owner));
    assert(s.holds_lock(owner));
    assert(forall|tid: Tid| s.in_ProcSet(tid) && s.holds_lock(tid) ==> tid == owner);
    owner
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
    tla_exists(
        |i: Tid|
            lift_state(|s: ProgramState| s.in_ProcSet(i) && s.trying(i)).leads_to(
                tla_exists(
                    |j: Tid| lift_state(|s: ProgramState| s.in_ProcSet(j) && s.pc[j] == Label::cs),
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

pub proof fn lemma_pc_stack_match(spec: TempPred<ProgramState>, n: nat)
    requires
        spec.entails(lift_state(init(n))),
        spec.entails(always(lift_action(next()))),
    ensures
        spec.entails(
            always(
                lift_state(
                    |s: ProgramState|
                        s.ProcSet.all(|tid: Tid| pc_stack_match(s.pc[tid], s.stack[tid])),
                ),
            ),
        ),
{
    lemma_inv_unchanged(spec, n);
    init_invariant(
        spec,
        init(n),
        next(),
        |s: ProgramState| { s.ProcSet.all(|tid: Tid| pc_stack_match(s.pc[tid], s.stack[tid])) },
    );
}


pub proof fn lemma_not_locked_iff_not_in_cs(spec: TempPred<ProgramState>, n: nat)
    requires
        spec.entails(lift_state(init(n))),
        spec.entails(always(lift_action(next()))),
    ensures
        spec.entails(always(lift_state(|s: ProgramState| s.not_locked_iff_no_cs()))),
{
    broadcast use group_tla_rules;
    lemma_inv_unchanged(spec, n);
    lemma_pc_stack_match(spec, n);
    let inv_unchanged_closure = |s: ProgramState| s.inv_unchanged(n);
    let pc_stack_match_closure = |s: ProgramState| s.ProcSet.all(|tid: Tid| pc_stack_match(s.pc[tid], s.stack[tid]));
    let not_locked_iff_no_cs_closure = |s: ProgramState| s.not_locked_iff_no_cs();
    assert forall |s: ProgramState, s_prime: ProgramState, tid: Tid|
        #[trigger] acquire_lock(tid)(s, s_prime) && s.inv_unchanged(n) && pc_stack_match_closure(s) && s.not_locked_iff_no_cs() implies 
            s_prime.not_locked_iff_no_cs() by {
                lemma_unlocked_means_no_holders(s);
                assert(pc_stack_match(s.pc[tid], s.stack[tid]));
                assert(s.pc[tid] == Label::lock);
                assert(s.stack[tid] =~= seq![
                    StackFrame { procedure: Procedure::acquire_lock, pc: Label::cs },
                ]);
                assert(s_prime.pc[tid] == Label::cs);
                assert(s_prime.locked);
                assert(s_prime.in_ProcSet(tid));
                assert(s_prime.holds_lock(tid));
                assert forall |tid2: Tid|
                    bool_implies(s_prime.in_ProcSet(tid2) && s_prime.holds_lock(tid2), tid2 == tid) by {
                    if s_prime.in_ProcSet(tid2) && s_prime.holds_lock(tid2) {
                        assert(tid2 == tid) by {
                            if tid2 == tid {
                            } else {
                                assert(s_prime.pc[tid2] == s.pc[tid2]);
                                if s_prime.pc[tid2] == Label::cs {
                                    assert(s.holds_lock(tid2));
                                } else {
                                    assert(s_prime.pc[tid2] == Label::unlock);
                                    assert(s.holds_lock(tid2));
                                }
                                assert(!s.holds_lock(tid2));
                                assert(false);
                            }
                        };
                    }
                };
            };
    assert forall |s: ProgramState, s_prime: ProgramState, tid: Tid|
        #[trigger] release_lock(tid)(s, s_prime) && s.inv_unchanged(n) && pc_stack_match_closure(s) && s.not_locked_iff_no_cs() implies 
            s_prime.not_locked_iff_no_cs() by {
                let owner = lemma_locked_unique_holder(s);
                assert(s.pc[tid] == Label::unlock);
                assert(s.holds_lock(tid));
                assert(forall|tid2: Tid| s.in_ProcSet(tid2) && s.holds_lock(tid2) ==> tid2 == owner);
                assert(tid == owner) by {
                    assert(s.in_ProcSet(tid));
                    assert(s.holds_lock(tid));
                };
                assert(pc_stack_match(s.pc[tid], s.stack[tid]));
                assert(s.stack[tid] =~= seq![
                    StackFrame { procedure: Procedure::release_lock, pc: Label::start },
                ]);
                assert(s_prime.pc[tid] == Label::start);
                assert(!s_prime.locked);
                assert forall|tid2: Tid|
                    bool_implies(s_prime.in_ProcSet(tid2), !s_prime.holds_lock(tid2)) by {
                    if s_prime.in_ProcSet(tid2) {
                        if tid2 == tid {
                            assert(s_prime.pc[tid2] == Label::start);
                            assert(!s_prime.holds_lock(tid2));
                        } else {
                            assert(s_prime.pc[tid2] == s.pc[tid2]);
                            if s.holds_lock(tid2) {
                                assert(tid2 == owner);
                                assert(false);
                            }
                            assert(!s_prime.holds_lock(tid2));
                        }
                    }
                };
            };
    assert forall |s: ProgramState, s_prime: ProgramState, tid: Tid|
        #[trigger] start().forward(tid)(s, s_prime) && s.inv_unchanged(n) && pc_stack_match_closure(s) && s.not_locked_iff_no_cs() implies 
            s_prime.not_locked_iff_no_cs() by {
                if s.locked {
                    let owner = lemma_locked_unique_holder(s);
                    assert(forall|tid2: Tid| s.in_ProcSet(tid2) && s.holds_lock(tid2) ==> tid2 == owner);
                    assert(s_prime.locked);
                    assert(s_prime.holds_lock(owner));
                    assert forall|tid2: Tid|
                        bool_implies(s_prime.in_ProcSet(tid2) && s_prime.holds_lock(tid2), tid2 == owner) by {
                        if s_prime.in_ProcSet(tid2) && s_prime.holds_lock(tid2) {
                            assert(tid2 == owner) by {
                                if tid2 == owner {
                                } else {
                                    assert(s_prime.pc[tid2] == s.pc[tid2]);
                                    assert(s.holds_lock(tid2));
                                    assert(tid2 == owner);
                                }
                            };
                        }
                    };
                } else {
                    lemma_unlocked_means_no_holders(s);
                    assert forall |tid2: Tid| bool_implies(s_prime.in_ProcSet(tid2), !s_prime.holds_lock(tid2)) by {
                        if s_prime.in_ProcSet(tid2) {
                            if tid2 == tid {
                                assert(s_prime.pc[tid2] == Label::lock);
                                assert(!s_prime.holds_lock(tid2));
                            } else {
                                assert(s_prime.pc[tid2] == s.pc[tid2]);
                                assert(!s.holds_lock(tid2));
                                assert(!s_prime.holds_lock(tid2));
                            }
                        }
                    };
                }
            };
    assert forall |s: ProgramState, s_prime: ProgramState, tid: Tid|
        #[trigger] cs().forward(tid)(s, s_prime) && s.inv_unchanged(n) && pc_stack_match_closure(s) && s.not_locked_iff_no_cs() implies 
            s_prime.not_locked_iff_no_cs() by {
                let owner = lemma_locked_unique_holder(s);
                assert(forall|tid2: Tid| s.in_ProcSet(tid2) && s.holds_lock(tid2) ==> tid2 == owner);
                assert(s.pc[tid] == Label::cs);
                assert(s.holds_lock(tid));
                assert(owner == tid) by {
                    assert(s.in_ProcSet(tid));
                    assert(s.holds_lock(tid));
                };
                assert(s_prime.locked);
                assert(s_prime.holds_lock(tid));
                assert forall|tid2: Tid|
                    bool_implies(s_prime.in_ProcSet(tid2) && s_prime.holds_lock(tid2), tid2 == tid) by {
                    if s_prime.in_ProcSet(tid2) && s_prime.holds_lock(tid2) {
                        assert(tid2 == tid) by {
                            if tid2 == tid {
                            } else {
                                assert(s_prime.pc[tid2] == s.pc[tid2]);
                                assert(s.holds_lock(tid2));
                                assert(tid2 == owner);
                            }
                        };
                    }
                };
            };
    
    assert forall |s: ProgramState| bool_implies(#[trigger] init(n)(s), not_locked_iff_no_cs_closure(s)) by {
        if init(n)(s) {
            assert(!s.locked);
            assert forall|tid: Tid| bool_implies(s.in_ProcSet(tid), !s.holds_lock(tid)) by {
                if s.in_ProcSet(tid) {
                    assert(s.pc[tid] == Label::start);
                    assert(!s.holds_lock(tid));
                }
            };
        }
    };

    assert forall |s: ProgramState, s_prime: ProgramState|
        bool_implies(
            #[trigger] next()(s, s_prime) && s.inv_unchanged(n) && pc_stack_match_closure(s)
                && s.not_locked_iff_no_cs(),
            s_prime.not_locked_iff_no_cs(),
        ) by {
        if next()(s, s_prime) && s.inv_unchanged(n) && pc_stack_match_closure(s)
            && s.not_locked_iff_no_cs()
        {
            let tid = choose|tid: Tid|
                s.in_ProcSet(tid) && (
                    acquire_lock(tid)(s, s_prime)
                    || release_lock(tid)(s, s_prime)
                    || start().forward(tid)(s, s_prime)
                    || cs().forward(tid)(s, s_prime)
                );
            if acquire_lock(tid)(s, s_prime) {
                assert(s_prime.not_locked_iff_no_cs());
            } else if release_lock(tid)(s, s_prime) {
                assert(s_prime.not_locked_iff_no_cs());
            } else if start().forward(tid)(s, s_prime) {
                assert(s_prime.not_locked_iff_no_cs());
            } else {
                assert(cs().forward(tid)(s, s_prime));
                assert(s_prime.not_locked_iff_no_cs());
            }
        }
    };
    strengthen_invariant_n!(spec, init(n), next(), not_locked_iff_no_cs_closure, inv_unchanged_closure, pc_stack_match_closure);
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
    let inv_unchanged_closure = |s: ProgramState| s.inv_unchanged(n);
    let not_locked_iff_no_cs_closure = |s: ProgramState| s.not_locked_iff_no_cs();
    let mutual_exclusion_closure = |s: ProgramState| s.mutual_exclusion();
    assert forall |s: ProgramState| s.inv_unchanged(n) && s.not_locked_iff_no_cs() implies #[trigger] s.mutual_exclusion() by {
        assert forall|i: Tid, j: Tid|
            bool_implies(
                s.in_ProcSet(i) && s.in_ProcSet(j) && i != j,
                !(s.pc[i] == Label::cs && s.pc[j] == Label::cs),
            ) by {
            if s.in_ProcSet(i) && s.in_ProcSet(j) && i != j {
                assert(!(s.pc[i] == Label::cs && s.pc[j] == Label::cs)) by {
                    if s.pc[i] == Label::cs && s.pc[j] == Label::cs {
                        if s.locked {
                            let owner = lemma_locked_unique_holder(s);
                            assert(i == owner) by {
                                assert(s.in_ProcSet(i));
                                assert(s.holds_lock(i));
                            };
                            assert(j == owner) by {
                                assert(s.in_ProcSet(j));
                                assert(s.holds_lock(j));
                            };
                            assert(i == j);
                            assert(false);
                        } else {
                            lemma_unlocked_means_no_holders(s);
                            assert(s.holds_lock(i));
                            assert(!s.holds_lock(i));
                            assert(false);
                        }
                    }
                };
            }
        };
    };
    always_lift_state_weaken_n!(
        spec,
        not_locked_iff_no_cs_closure,
        inv_unchanged_closure,
        mutual_exclusion_closure,
    );
}


} // verus!
