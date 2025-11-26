use vstd::prelude::*;
use vstd::set_lib::*;
use vstd_extra::{set_extra::*,state_machine::*, temporal_logic::*};

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

    pub open spec fn not_locked_iff_no_cs(self) -> bool {
        (!self.locked <==> self.ProcSet.filter(|tid: Tid| self.pc[tid] == Label::cs || self.pc[tid] == Label::unlock).is_empty()) &&
        (self.locked <==> self.ProcSet.filter(|tid: Tid| self.pc[tid] == Label::cs || self.pc[tid] == Label::unlock).is_singleton())
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
                admit();
            };
    assert forall |s: ProgramState, s_prime: ProgramState, tid: Tid|
        #[trigger] release_lock(tid)(s, s_prime) && s.inv_unchanged(n) && pc_stack_match_closure(s) && s.not_locked_iff_no_cs() implies 
            s_prime.not_locked_iff_no_cs() by {
                admit();
            };
    assert forall |s: ProgramState, s_prime: ProgramState, tid: Tid|
        #[trigger] start().forward(tid)(s, s_prime) && s.inv_unchanged(n) && pc_stack_match_closure(s) && s.not_locked_iff_no_cs() implies 
            s_prime.not_locked_iff_no_cs() by {
                admit();
            };
    assert forall |s: ProgramState, s_prime: ProgramState, tid: Tid|
        #[trigger] cs().forward(tid)(s, s_prime) && s.inv_unchanged(n) && pc_stack_match_closure(s) && s.not_locked_iff_no_cs() implies 
            s_prime.not_locked_iff_no_cs() by {
                admit();
            };
    
    assert (forall|s: ProgramState, s_prime: ProgramState|
        #[trigger] next()(s, s_prime) && s.inv_unchanged(n) && pc_stack_match_closure(s) && s.not_locked_iff_no_cs() ==> 
            s_prime.not_locked_iff_no_cs());
    strengthen_invariant_n!(spec, init(n), next(), not_locked_iff_no_cs_closure, inv_unchanged_closure, pc_stack_match_closure);
}

#[verifier::external_body]
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
        lemma_set_prop_mutual_exclusion(s.ProcSet, |tid: Tid| s.pc[tid] == Label::cs);
        assert(s.ProcSet.filter(|tid: Tid| s.pc[tid] == Label::cs).len() <= 1) by {
            Set::lemma_is_singleton(s.ProcSet.filter(|tid: Tid| s.pc[tid] == Label::cs));
        }
    };
    always_lift_state_weaken_n!(
        spec,
        not_locked_iff_no_cs_closure,
        inv_unchanged_closure,
        mutual_exclusion_closure,
    );
}


} // verus!
