// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::defs::*;
use vstd::map_lib::*;
use vstd::prelude::*;

// Internal lemmas about executions and temporal predicates.
verus! {

broadcast proof fn lemma_execution_sufix_0<T>(ex: Execution<T>)
    ensures
        #[trigger] ex.suffix(0) == ex,
{
}

broadcast proof fn lemma_execution_sufix_sufix<T>(ex: Execution<T>, i: nat, j: nat)
    ensures
        #[trigger] ex.suffix(i).suffix(j) == ex.suffix(i + j),
{
}

broadcast group group_execution_suffix_lemmas {
    lemma_execution_sufix_0,
    lemma_execution_sufix_sufix,
}

} // verus!
verus! {

broadcast proof fn implies_apply<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        #[trigger] p.implies(q).satisfied_by(ex),
        p.satisfied_by(ex),
    ensures
        q.satisfied_by(ex),
{
}

proof fn implies_contraposition_apply<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        p.implies(q).satisfied_by(ex),
        not(q).satisfied_by(ex),
    ensures
        not(p).satisfied_by(ex),
{
}

pub proof fn temp_pred_equality<T>(p: TempPred<T>, q: TempPred<T>)
    requires
        p.entails(q),
        q.entails(p),
    ensures
        p == q,
{
    assert forall|ex: Execution<T>| #[trigger] (p.pred)(ex) == (q.pred)(ex) by {
        if (p.pred)(ex) {
            implies_apply::<T>(ex, p, q);
        } else {
            implies_contraposition_apply::<T>(ex, q, p);
        }
    };
}

proof fn later_unfold<T>(ex: Execution<T>, p: TempPred<T>)
    requires
        later(p).satisfied_by(ex),
    ensures
        p.satisfied_by(ex.suffix(1)),
{
}

broadcast proof fn always_unfold<T>(ex: Execution<T>, p: TempPred<T>)
    requires
        #[trigger] always(p).satisfied_by(ex),
    ensures
        forall|i: nat| p.satisfied_by(#[trigger] ex.suffix(i)),
{
}

proof fn eventually_unfold<T>(ex: Execution<T>, p: TempPred<T>)
    requires
        eventually(p).satisfied_by(ex),
    ensures
        exists|i: nat| p.satisfied_by(#[trigger] ex.suffix(i)),
{
}

proof fn not_eventually_unfold<T>(ex: Execution<T>, p: TempPred<T>)
    requires
        not(eventually(p)).satisfied_by(ex),
    ensures
        forall|i| !p.satisfied_by(#[trigger] ex.suffix(i)),
{
}

proof fn stable_unfold<T>(ex: Execution<T>, p: TempPred<T>)
    requires
        stable(p).satisfied_by(ex),
    ensures
        p.satisfied_by(ex) ==> forall|i| p.satisfied_by(#[trigger] ex.suffix(i)),
{
}

proof fn leads_to_unfold<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        p.leads_to(q).satisfied_by(ex),
    ensures
        forall|i: nat| p.implies(eventually(q)).satisfied_by(#[trigger] ex.suffix(i)),
{
}

proof fn weak_fairness_unfold<T>(ex: Execution<T>, p: ActionPred<T>)
    requires
        weak_fairness(p).satisfied_by(ex),
    ensures
        forall|i|
            always(lift_state(enabled(p))).implies(eventually(lift_action(p))).satisfied_by(
                #[trigger] ex.suffix(i),
            ),
{
}

proof fn always_lift_state_unfold<T>(ex: Execution<T>, p: StatePred<T>)
    requires
        always(lift_state(p)).satisfied_by(ex),
    ensures
        forall|i| p.apply(#[trigger] ex.suffix(i).head()),
{
    broadcast use always_unfold;

}

proof fn always_lift_action_unfold<T>(ex: Execution<T>, p: ActionPred<T>)
    requires
        always(lift_action(p)).satisfied_by(ex),
    ensures
        forall|i| p.apply(#[trigger] ex.suffix(i).head(), ex.suffix(i).head_next()),
{
    broadcast use always_unfold;

}

broadcast proof fn tla_forall_unfold<T, A>(
    ex: Execution<T>,
    a_to_temp_pred: spec_fn(A) -> TempPred<T>,
)
    requires
        #[trigger] tla_forall(a_to_temp_pred).satisfied_by(ex),
    ensures
        forall|a| #[trigger] a_to_temp_pred(a).satisfied_by(ex),
{
}

broadcast proof fn tla_exists_unfold<T, A>(
    ex: Execution<T>,
    a_to_temp_pred: spec_fn(A) -> TempPred<T>,
)
    requires
        #[trigger] tla_exists(a_to_temp_pred).satisfied_by(ex),
    ensures
        exists|a| #[trigger] a_to_temp_pred(a).satisfied_by(ex),
{
}

proof fn tla_exists_proved_by_witness<T, A>(
    ex: Execution<T>,
    a_to_temp_pred: spec_fn(A) -> TempPred<T>,
    witness_a: A,
)
    requires
        a_to_temp_pred(witness_a).satisfied_by(ex),
    ensures
        tla_exists(a_to_temp_pred).satisfied_by(ex),
{
}

spec fn tla_exists_choose_witness<T, A>(
    ex: Execution<T>,
    a_to_temp_pred: spec_fn(A) -> TempPred<T>,
) -> A
    recommends
        exists|a| #[trigger] a_to_temp_pred(a).satisfied_by(ex),
{
    let witness = choose|a| #[trigger] a_to_temp_pred(a).satisfied_by(ex);
    witness
}

proof fn implies_apply_with_always<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        always(p.implies(q)).satisfied_by(ex),
        always(p).satisfied_by(ex),
    ensures
        always(q).satisfied_by(ex),
{
    broadcast use always_unfold;

}

proof fn entails_apply<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        p.entails(q),
        p.satisfied_by(ex),
    ensures
        q.satisfied_by(ex),
{
    implies_apply::<T>(ex, p, q);
}

proof fn not_proved_by_contraposition<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        p.implies(q).satisfied_by(ex),
        not(q).satisfied_by(ex),
    ensures
        not(p).satisfied_by(ex),
{
}

proof fn not_eventually_by_always_not<T>(ex: Execution<T>, p: TempPred<T>)
    requires
        always(not(p)).satisfied_by(ex),
    ensures
        not(eventually(p)).satisfied_by(ex),
{
    broadcast use always_unfold;

}

broadcast proof fn always_propagate_forwards<T>(ex: Execution<T>, p: TempPred<T>, i: nat)
    requires
        always(p).satisfied_by(ex),
    ensures
        #[trigger] always(p).satisfied_by(ex.suffix(i)),
{
    broadcast use {always_unfold, group_execution_suffix_lemmas};

}

proof fn always_double<T>(ex: Execution<T>, p: TempPred<T>)
    requires
        always(p).satisfied_by(ex),
    ensures
        always(always(p)).satisfied_by(ex),
{
    broadcast use {always_unfold, always_propagate_forwards};

}

proof fn always_to_current<T>(ex: Execution<T>, p: TempPred<T>)
    requires
        always(p).satisfied_by(ex),
    ensures
        p.satisfied_by(ex),
{
    assert(ex == ex.suffix(0));
}

proof fn always_to_future<T>(ex: Execution<T>, p: TempPred<T>, i: nat)
    requires
        always(p).satisfied_by(ex),
    ensures
        p.satisfied_by(ex.suffix(i)),
{
    broadcast use {always_unfold, always_propagate_forwards};

}

proof fn eventually_propagate_backwards<T>(ex: Execution<T>, p: TempPred<T>, i: nat)
    requires
        eventually(p).satisfied_by(ex.suffix(i)),
    ensures
        eventually(p).satisfied_by(ex),
{
    broadcast use group_execution_suffix_lemmas;

}

proof fn eventually_proved_by_witness<T>(ex: Execution<T>, p: TempPred<T>, witness_idx: nat)
    requires
        p.satisfied_by(ex.suffix(witness_idx)),
    ensures
        eventually(p).satisfied_by(ex),
{
}

spec fn eventually_choose_witness<T>(ex: Execution<T>, p: TempPred<T>) -> nat
    recommends
        exists|i| p.satisfied_by(#[trigger] ex.suffix(i)),
{
    let witness = choose|i| p.satisfied_by(#[trigger] ex.suffix(i));
    witness
}

proof fn valid_p_implies_always_p<T>(p: TempPred<T>)
    requires
        valid(p),
    ensures
        valid(always(p)),
{
}

proof fn always_distributed_by_and<T>(p: TempPred<T>, q: TempPred<T>)
    ensures
        valid(always(p.and(q)).implies(always(p).and(always(q)))),
{
    broadcast use always_unfold;

}

proof fn p_and_always_p_equals_always_p<T>(p: TempPred<T>)
    ensures
        p.and(always(p)) == always(p),
{
    assert forall|ex| #[trigger] always(p).satisfied_by(ex) implies p.and(always(p)).satisfied_by(
        ex,
    ) by {
        always_to_current::<T>(ex, p);
    };
    temp_pred_equality::<T>(p.and(always(p)), always(p));
}

proof fn a_to_temp_pred_equality<T, A>(p: spec_fn(A) -> TempPred<T>, q: spec_fn(A) -> TempPred<T>)
    requires
        forall|a: A| #[trigger] p(a).entails(q(a)) && q(a).entails(p(a)),
    ensures
        p == q,
{
    assert forall|a: A| #[trigger] p(a) == q(a) by {
        temp_pred_equality::<T>(p(a), q(a));
    };
}

proof fn tla_forall_or_equality<T, A>(a_to_temp_pred: spec_fn(A) -> TempPred<T>, q: TempPred<T>)
    ensures
        tla_forall(|a: A| a_to_temp_pred(a).or(q)) == tla_forall(a_to_temp_pred).or(q),
{
    broadcast use tla_forall_unfold;

    let a_to_temp_pred_or_q = |a: A| a_to_temp_pred(a).or(q);
    assert forall|ex| #[trigger] tla_forall(a_to_temp_pred_or_q).satisfied_by(ex) implies (
    tla_forall(a_to_temp_pred).or(q)).satisfied_by(ex) by {
        if !q.satisfied_by(ex) {
            assert forall|a| #[trigger] a_to_temp_pred(a).satisfied_by(ex) by {
                assert(a_to_temp_pred_or_q(a).satisfied_by(ex));
            };
        }
    };
    temp_pred_equality::<T>(
        tla_forall(|a: A| a_to_temp_pred(a).or(q)),
        tla_forall(a_to_temp_pred).or(q),
    );
}

proof fn tla_exists_and_equality<T, A>(a_to_temp_pred: spec_fn(A) -> TempPred<T>, q: TempPred<T>)
    ensures
        tla_exists(|a: A| a_to_temp_pred(a).and(q)) == tla_exists(a_to_temp_pred).and(q),
{
    let a_to_temp_pred_and_q = |a: A| a_to_temp_pred(a).and(q);
    assert forall|ex| #[trigger]
        (tla_exists(a_to_temp_pred).and(q)).satisfied_by(ex) implies tla_exists(
        a_to_temp_pred_and_q,
    ).satisfied_by(ex) by {
        let witness_a = tla_exists_choose_witness::<T, A>(ex, a_to_temp_pred);
        tla_exists_proved_by_witness::<T, A>(ex, a_to_temp_pred_and_q, witness_a);
    };
    temp_pred_equality::<T>(
        tla_exists(|a: A| a_to_temp_pred(a).and(q)),
        tla_exists(a_to_temp_pred).and(q),
    );
}

proof fn tla_exists_or_equality<T, A>(a_to_temp_pred: spec_fn(A) -> TempPred<T>, q: TempPred<T>)
    ensures
        tla_exists(|a: A| a_to_temp_pred(a).or(q)) == tla_exists(a_to_temp_pred).or(q),
{
    let a_to_temp_pred_or_q = |a: A| a_to_temp_pred(a).or(q);
    assert forall|ex| #[trigger]
        (tla_exists(a_to_temp_pred).or(q)).satisfied_by(ex) implies tla_exists(
        a_to_temp_pred_or_q,
    ).satisfied_by(ex) by {
        if !q.satisfied_by(ex) {
            let witness_a = tla_exists_choose_witness::<T, A>(ex, a_to_temp_pred);
            tla_exists_proved_by_witness::<T, A>(ex, a_to_temp_pred_or_q, witness_a);
        } else {
            assert(a_to_temp_pred_or_q(arbitrary()).satisfied_by(ex));
        }
    };
    temp_pred_equality::<T>(
        tla_exists(|a: A| a_to_temp_pred(a).or(q)),
        tla_exists(a_to_temp_pred).or(q),
    );
}

proof fn tla_forall_implies_equality1<T, A>(
    a_to_temp_pred: spec_fn(A) -> TempPred<T>,
    q: TempPred<T>,
)
    ensures
        tla_forall(|a: A| a_to_temp_pred(a).implies(q)) == tla_exists(a_to_temp_pred).implies(q),
{
    let a_to_not_p = |a: A| not(a_to_temp_pred(a));
    a_to_temp_pred_equality::<T, A>(
        |a: A| a_to_temp_pred(a).implies(q),
        |a: A| a_to_not_p(a).or(q),
    );
    temp_pred_equality::<T>(
        tla_forall(|a: A| a_to_temp_pred(a).implies(q)),
        tla_forall(|a: A| a_to_not_p(a).or(q)),
    );
    tla_forall_or_equality::<T, A>(a_to_not_p, q);
    tla_forall_not_equality::<T, A>(a_to_temp_pred);
    temp_pred_equality::<T>(
        not(tla_exists(a_to_temp_pred)).or(q),
        tla_exists(a_to_temp_pred).implies(q),
    );
}

proof fn tla_forall_implies_equality2<T, A>(
    p: TempPred<T>,
    a_to_temp_pred: spec_fn(A) -> TempPred<T>,
)
    ensures
        tla_forall(|a: A| p.implies(a_to_temp_pred(a))) == p.implies(tla_forall(a_to_temp_pred)),
{
    a_to_temp_pred_equality::<T, A>(
        |a: A| p.implies(a_to_temp_pred(a)),
        |a: A| a_to_temp_pred(a).or(not(p)),
    );
    temp_pred_equality::<T>(
        tla_forall(|a: A| p.implies(a_to_temp_pred(a))),
        tla_forall(|a: A| a_to_temp_pred(a).or(not(p))),
    );
    tla_forall_or_equality::<T, A>(a_to_temp_pred, not(p));
    temp_pred_equality::<T>(
        tla_forall(a_to_temp_pred).or(not(p)),
        p.implies(tla_forall(a_to_temp_pred)),
    );
}

proof fn tla_exists_implies_equality1<T, A>(
    p: TempPred<T>,
    a_to_temp_pred: spec_fn(A) -> TempPred<T>,
)
    ensures
        tla_exists(|a: A| p.implies(a_to_temp_pred(a))) == p.implies(tla_exists(a_to_temp_pred)),
{
    a_to_temp_pred_equality::<T, A>(
        |a: A| p.implies(a_to_temp_pred(a)),
        |a: A| a_to_temp_pred(a).or(not(p)),
    );
    temp_pred_equality::<T>(
        tla_exists(|a: A| p.implies(a_to_temp_pred(a))),
        tla_exists(|a: A| a_to_temp_pred(a).or(not(p))),
    );
    tla_exists_or_equality::<T, A>(a_to_temp_pred, not(p));
    temp_pred_equality::<T>(
        tla_exists(a_to_temp_pred).or(not(p)),
        p.implies(tla_exists(a_to_temp_pred)),
    );
}

proof fn tla_forall_leads_to_equality1<T, A>(
    a_to_temp_pred: spec_fn(A) -> TempPred<T>,
    q: TempPred<T>,
)
    ensures
        tla_forall(|a: A| a_to_temp_pred(a).leads_to(q)) == tla_exists(a_to_temp_pred).leads_to(q),
{
    tla_forall_always_equality_variant::<T, A>(
        |a: A| a_to_temp_pred(a).leads_to(q),
        |a: A| a_to_temp_pred(a).implies(eventually(q)),
    );
    tla_forall_implies_equality1::<T, A>(a_to_temp_pred, eventually(q));
}

proof fn tla_forall_always_implies_equality2<T, A>(
    p: TempPred<T>,
    a_to_temp_pred: spec_fn(A) -> TempPred<T>,
)
    ensures
        tla_forall(|a: A| always(p.implies(a_to_temp_pred(a)))) == always(
            p.implies(tla_forall(a_to_temp_pred)),
        ),
{
    tla_forall_always_equality_variant::<T, A>(
        |a: A| always(p.implies(a_to_temp_pred(a))),
        |a: A| p.implies(a_to_temp_pred(a)),
    );
    tla_forall_implies_equality2::<T, A>(p, a_to_temp_pred);
}

proof fn tla_forall_not_equality<T, A>(a_to_temp_pred: spec_fn(A) -> TempPred<T>)
    ensures
        tla_forall(|a: A| not(a_to_temp_pred(a))) == not(tla_exists(a_to_temp_pred)),
{
    let a_to_not_p = |a: A| not(a_to_temp_pred(a));
    assert forall|ex| #[trigger] tla_forall(a_to_not_p).satisfied_by(ex) implies not(
        tla_exists(a_to_temp_pred),
    ).satisfied_by(ex) by {
        assert forall|a| !#[trigger] a_to_temp_pred(a).satisfied_by(ex) by {
            assert(a_to_not_p(a).satisfied_by(ex));
        };
    };
    temp_pred_equality::<T>(
        tla_forall(|a: A| not(a_to_temp_pred(a))),
        not(tla_exists(a_to_temp_pred)),
    );
}

proof fn tla_forall_and_equality<T, A>(a_to_temp_pred: spec_fn(A) -> TempPred<T>, q: TempPred<T>)
    ensures
        tla_forall(|a: A| a_to_temp_pred(a).and(q)) == tla_forall(a_to_temp_pred).and(q),
{
    broadcast use tla_forall_unfold;

    let a_to_temp_pred_and_q = |a: A| a_to_temp_pred(a).and(q);
    assert forall|ex| #[trigger] tla_forall(a_to_temp_pred_and_q).satisfied_by(ex) implies (
    tla_forall(a_to_temp_pred).and(q)).satisfied_by(ex) by {
        assert forall|a| #[trigger] a_to_temp_pred(a).satisfied_by(ex) by {
            assert(a_to_temp_pred_and_q(a).satisfied_by(ex));
        };
        assert(a_to_temp_pred_and_q(arbitrary()).satisfied_by(ex));
    };
    temp_pred_equality::<T>(
        tla_forall(|a: A| a_to_temp_pred(a).and(q)),
        tla_forall(a_to_temp_pred).and(q),
    );
}

proof fn init_invariant_rec<T>(
    ex: Execution<T>,
    init: StatePred<T>,
    next: ActionPred<T>,
    inv: StatePred<T>,
    i: nat,
)
    requires
        lift_state(init).satisfied_by(ex),
        always(lift_action(next)).satisfied_by(ex),
        lift_state(init).implies(lift_state(inv)).satisfied_by(ex),
        forall|idx: nat|
            inv.apply(#[trigger] ex.suffix(idx).head()) && next.apply(
                ex.suffix(idx).head(),
                ex.suffix(idx).head_next(),
            ) ==> inv.apply(ex.suffix(idx).head_next()),
    ensures
        inv.apply(ex.suffix(i).head()),
    decreases i,
{
    broadcast use {always_unfold, group_execution_suffix_lemmas};

    if i != 0 {
        init_invariant_rec::<T>(ex, init, next, inv, (i - 1) as nat);
    }
}

proof fn implies_new_invariant_rec<T>(
    ex: Execution<T>,
    init: StatePred<T>,
    next: ActionPred<T>,
    inv: StatePred<T>,
    proved_inv: StatePred<T>,
    i: nat,
)
    requires
        lift_state(init).satisfied_by(ex),
        always(lift_action(next)).satisfied_by(ex),
        always(lift_state(proved_inv)).satisfied_by(ex),
        lift_state(init).implies(lift_state(inv)).satisfied_by(ex),
        forall|idx: nat|
            inv.apply(#[trigger] ex.suffix(idx).head()) && proved_inv.apply(
                #[trigger] ex.suffix(idx).head(),
            ) && next.apply(ex.suffix(idx).head(), ex.suffix(idx).head_next()) ==> inv.apply(
                ex.suffix(idx).head_next(),
            ),
    ensures
        inv.apply(ex.suffix(i).head()),
    decreases i,
{
    broadcast use {always_unfold, group_execution_suffix_lemmas};

    if i != 0 {
        implies_new_invariant_rec(ex, init, next, inv, proved_inv, (i - 1) as nat);
    }
}

proof fn always_p_or_eventually_q_rec<T>(
    ex: Execution<T>,
    next: TempPred<T>,
    p: TempPred<T>,
    q: TempPred<T>,
    i: nat,
)
    requires
        always(p.and(next).implies(later(p).or(later(q)))).satisfied_by(ex),
        always(next).satisfied_by(ex),
        always(not(q)).satisfied_by(ex),
        p.satisfied_by(ex),
    ensures
        p.satisfied_by(ex.suffix(i)),
    decreases i,
{
    broadcast use {always_unfold, group_execution_suffix_lemmas};

    if i != 0 {
        always_p_or_eventually_q_rec::<T>(ex, next, p, q, (i - 1) as nat);
    }
}

proof fn always_p_or_eventually_q<T>(
    ex: Execution<T>,
    next: TempPred<T>,
    p: TempPred<T>,
    q: TempPred<T>,
)
    requires
        always(p.and(next).implies(later(p).or(later(q)))).satisfied_by(ex),
        always(next).satisfied_by(ex),
    ensures
        always(p.implies(always(p).or(eventually(q)))).satisfied_by(ex),
{
    broadcast use {always_unfold, implies_apply, group_execution_suffix_lemmas};

    assert forall|i| p.satisfied_by(#[trigger] ex.suffix(i)) implies always(p).satisfied_by(
        ex.suffix(i),
    ) || eventually(q).satisfied_by(ex.suffix(i)) by {
        if !eventually(q).satisfied_by(ex.suffix(i)) {
            assert forall|j| p.satisfied_by(#[trigger] ex.suffix(i).suffix(j)) by {
                always_p_or_eventually_q_rec::<T>(ex.suffix(i), next, p, q, j);
            };
        }
    };
}

proof fn next_preserves_inv_rec<T>(ex: Execution<T>, next: TempPred<T>, inv: TempPred<T>, i: nat)
    requires
        inv.satisfied_by(ex),
        always(next).satisfied_by(ex),
        always(inv.and(next).implies(later(inv))).satisfied_by(ex),
    ensures
        inv.satisfied_by(ex.suffix(i)),
    decreases i,
{
    broadcast use {always_unfold, group_execution_suffix_lemmas};

    if i != 0 {
        next_preserves_inv_rec::<T>(ex, next, inv, (i - 1) as nat);
    }
}

proof fn instantiate_entailed_always<T>(ex: Execution<T>, i: nat, spec: TempPred<T>, p: TempPred<T>)
    requires
        spec.satisfied_by(ex),
        spec.implies(always(p)).satisfied_by(ex),
    ensures
        p.satisfied_by(ex.suffix(i)),
{
    broadcast use {always_unfold, implies_apply};

}

proof fn instantiate_entailed_leads_to<T>(
    ex: Execution<T>,
    i: nat,
    spec: TempPred<T>,
    p: TempPred<T>,
    q: TempPred<T>,
)
    requires
        spec.satisfied_by(ex),
        spec.implies(p.leads_to(q)).satisfied_by(ex),
    ensures
        p.implies(eventually(q)).satisfied_by(ex.suffix(i)),
{
    broadcast use implies_apply;

}

} // verus!
// Public lemmas about temporal logic for developers to simplify liveness/safety proofs.
verus! {

// Basic Rules of Temporal Logic Operators
/// Lift `StatePred::and` to Verus meta-level.
pub broadcast proof fn state_pred_and_apply_equality<T>(p: StatePred<T>, q: StatePred<T>, s: T)
    ensures
        #[trigger] p.and(q).apply(s) == (p.apply(s) && q.apply(s)),
{
}

/// Lift `StatePred::or` to Verus meta-level.
pub broadcast proof fn state_pred_or_apply_equality<T>(p: StatePred<T>, q: StatePred<T>, s: T)
    ensures
        #[trigger] p.or(q).apply(s) == (p.apply(s) || q.apply(s)),
{
}

/// Lift `StatePred::not` to Verus meta-level.
pub broadcast proof fn state_pred_not_apply_equality<T>(p: StatePred<T>, s: T)
    ensures
        #[trigger] p.not().apply(s) == !p.apply(s),
{
}

/// Lift `StatePred::implies` to Verus meta-level.
pub broadcast proof fn state_pred_implies_apply_equality<T>(p: StatePred<T>, q: StatePred<T>, s: T)
    ensures
        #[trigger] p.implies(q).apply(s) == (p.apply(s) ==> q.apply(s)),
{
}

/// `StatePred::and` distributes over `lift_state`.
/// 
/// ## Postconditions  
/// - `lift_state(p ∧ q) == lift_state(p) ∧ lift_state(q)`
pub broadcast proof fn lift_state_and_equality<T>(p: StatePred<T>, q: StatePred<T>)
    ensures
        #![trigger lift_state(p.and(q))]
        #![trigger lift_state(p).and(lift_state(q))]
        lift_state(p.and(q)) == lift_state(p).and(lift_state(q)),
{
}

/// `StatePred::or` distributes over `lift_state`.
/// 
/// ## Postconditions  
/// - `lift_state(p ∨ q) == lift_state(p) ∨ lift_state(q)`
pub broadcast proof fn lift_state_or_equality<T>(p: StatePred<T>, q: StatePred<T>)
    ensures
        #![trigger lift_state(p.or(q))]
        #![trigger lift_state(p).or(lift_state(q))]
        lift_state(p.or(q)) == lift_state(p).or(lift_state(q)),
{
}

/// `StatePred::not` distributes over `lift_state`.
/// 
/// ## Postconditions  
/// - `lift_state(!p) == !lift_state(p)`
pub broadcast proof fn lift_state_not_equality<T>(p: StatePred<T>)
    ensures
        #![trigger lift_state(p.not())]
        #![trigger not(lift_state(p))]
        lift_state(p.not()) == not(lift_state(p)),
{
}

/// `StatePred::implies` distributes over `lift_state`.
///
/// ## Postconditions  
/// - `lift_state(p ⇒ q) == lift_state(p) ⇒ lift_state(q)`
pub broadcast proof fn lift_state_implies_equality<T>(p: StatePred<T>, q: StatePred<T>)
    ensures
        #[trigger] lift_state(p.implies(q)) == lift_state(p).implies(lift_state(q)),
{
}

/// `StatePred::and` distributes over `□`.
///
/// ## Postconditions  
/// - `□(p ∧ q) == □p ∧ □q`
pub broadcast proof fn always_and_equality<T>(p: TempPred<T>, q: TempPred<T>)
    ensures
        #[trigger] always(p.and(q)) == always(p).and(always(q)),
{
    broadcast use always_unfold;

    temp_pred_equality::<T>(always(p.and(q)), always(p).and(always(q)));
}

/// Lift entails `TempPred::and` to Verus meta-level.
/// 
/// If `⊧ p` and `⊧ q`, then `⊧ p ∧ q`.
/// 
/// ## Preconditions
/// - `spec ⊧ p`  
/// - `spec ⊧ q`  
/// ## Postconditions
/// - `spec ⊧ p ∧ q`
pub broadcast proof fn entails_and_temp<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec.entails(p),
        spec.entails(q),
    ensures
        #[trigger] spec.entails(p.and(q)),
{
    assert forall|ex| #[trigger] spec.satisfied_by(ex) implies p.and(q).satisfied_by(ex) by {
        implies_apply::<T>(ex, spec, p);
        implies_apply::<T>(ex, spec, q);
    };
}

/// Lift entails `TempPred::and` to Verus meta-level (reversed direction).
/// 
/// If `⊧ p ∧ q`, then `⊧ p` and `⊧ q`.
///
/// ## Preconditions  
/// - `spec ⊧ p ∧ q`
/// ## Postconditions  
/// - `spec ⊧ p`
/// - `spec ⊧ q`
pub broadcast proof fn entails_and_temp_reverse<T>(
    spec: TempPred<T>,
    p: TempPred<T>,
    q: TempPred<T>,
)
    requires
        #[trigger] spec.entails(p.and(q)),
    ensures
        spec.entails(p),
        spec.entails(q),
{
    assert forall|ex| #[trigger] spec.satisfied_by(ex) implies p.satisfied_by(ex) by {
        implies_apply::<T>(ex, spec, p.and(q));
    };
    assert forall|ex| #[trigger] spec.satisfied_by(ex) implies q.satisfied_by(ex) by {
        implies_apply::<T>(ex, spec, p.and(q));
    };
}

/// Lift entails `TempPred::or` to Verus meta-level.
/// 
/// If `⊧ p` or `⊧ q`, then `⊧ p ∨ q`.
///
/// ## Preconditions  
/// - `spec ⊧ p` or `spec ⊧ q`
/// ## Postconditions  
/// - `spec ⊧ p ∨ q`
///
/// NOTE: The other direction does not hold in general.
pub broadcast proof fn entails_or_temp<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec.entails(p) || spec.entails(q),
    ensures
        #[trigger] spec.entails(p.or(q)),
{
    assert forall|ex| #[trigger] spec.satisfied_by(ex) implies p.or(q).satisfied_by(ex) by {
        if spec.entails(p) {
            implies_apply::<T>(ex, spec, p);
        } else {
            implies_apply::<T>(ex, spec, q);
        }
    };
}

/// Lift entails `TempPred::not` to Verus meta-level (reversed direction).
/// 
/// If `⊧ !p`, then `!(⊧ p)`.
///
/// ## Preconditions  
/// - `spec ⊧ !p`
/// ## Postconditions  
/// - `!(spec ⊧ p)`
///
/// NOTE: The other direction does not hold in general.
pub broadcast proof fn entails_not_temp_reverse<T>(spec: TempPred<T>, p: TempPred<T>)
    requires
        #[trigger] spec.entails(not(p)),
        spec != false_pred::<T>(),
    ensures
        !spec.entails(p),
{
    if forall|ex| !#[trigger] spec.satisfied_by(ex) {
        temp_pred_equality::<T>(spec, false_pred::<T>());
    }
    let ex = choose|ex| spec.satisfied_by(ex);
    assert(spec.implies(not(p)).satisfied_by(ex));
    assert(!spec.implies(p).satisfied_by(ex));
}

/// Lift entails `TempPred::implies` to Verus meta-level.
/// 
/// If `⊧ p ⇒ q`, then `⊧ p` implies `⊧ q`.
/// 
/// ## Preconditions  
/// - `spec ⊧ (p ⇒ q)`
/// ## Postconditions  
/// - `(spec ⊧ p) ⇒ (spec ⊧ q)`
/// 
/// NOTE: The other direction does not hold in general.
pub broadcast proof fn entails_implies_temp_reverse<T>(
    spec: TempPred<T>,
    p: TempPred<T>,
    q: TempPred<T>,
)
    requires
        #[trigger] spec.entails(p.implies(q)),
    ensures
        spec.entails(p) ==> spec.entails(q),
{
    if spec.entails(p) {
        assert forall|ex| #[trigger] spec.satisfied_by(ex) implies q.satisfied_by(ex) by {
            implies_apply::<T>(ex, spec, p.implies(q));
            implies_apply::<T>(ex, spec, p);
        };
    }
}

broadcast group group_definition_basics {
    state_pred_and_apply_equality,
    state_pred_or_apply_equality,
    state_pred_not_apply_equality,
    state_pred_implies_apply_equality,
    lift_state_and_equality,
    lift_state_or_equality,
    lift_state_not_equality,
    lift_state_implies_equality,
    always_and_equality,
    entails_and_temp,
    entails_and_temp_reverse,
    entails_or_temp,
    entails_not_temp_reverse,
    entails_implies_temp_reverse,
}

/// Double `□` can be simplified.
/// 
/// ## Postconditions  
/// - `□□p == □p`
pub broadcast proof fn always_double_equality<T>(p: TempPred<T>)
    ensures
        #[trigger] always(always(p)) == always(p),
{
    broadcast use {always_unfold, group_execution_suffix_lemmas};

    assert forall|ex| #[trigger] always(always(p)).satisfied_by(ex) implies always(p).satisfied_by(
        ex,
    ) by {
        assert(always(p).satisfied_by(ex.suffix(0)));
    }
    temp_pred_equality::<T>(always(always(p)), always(p));
}

/// `StatePred::and` distributes over `□` and `lift_state`.
///
/// ## Postconditions
/// - `□(lift_state(p ∧ q)) == □lift_state(p) ∧ □lift_state(q)`
pub broadcast proof fn always_lift_state_and_equality<T>(p: StatePred<T>, q: StatePred<T>)
    ensures
        #[trigger] always(lift_state(p.and(q))) == always(lift_state(p)).and(always(lift_state(q))),
{
    broadcast use group_definition_basics;

}

/// Obviously `p ⇝ p` is valid.
/// 
/// ## Postconditions  
/// - `⊧ p ⇝ p`
pub broadcast proof fn leads_to_self_temp<T>(p: TempPred<T>)
    ensures
        #[trigger] valid(p.leads_to(p)),
{
    broadcast use group_definition_basics;

    assert forall|ex| #[trigger] always(p.implies(eventually(p))).satisfied_by(ex) by {
        assert forall|i| #[trigger] p.satisfied_by(ex.suffix(i)) implies eventually(p).satisfied_by(
            ex.suffix(i),
        ) by {
            assert(ex.suffix(i) == ex.suffix(i).suffix(0));
            eventually_proved_by_witness::<T>(ex.suffix(i), p, 0);
        };
    };
}

/// Entails is transitive.
/// 
/// ## Preconditions  
/// - `p ⊧ q`  
/// - `q ⊧ r`  
/// ## Postconditions  
/// - `p ⊧ r`  
pub proof fn entails_trans<T>(p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        p.entails(q),
        q.entails(r),
    ensures
        p.entails(r),
{
    assert forall|ex| p.satisfied_by(ex) implies r.satisfied_by(ex) by {
        implies_apply::<T>(ex, p, q);
        implies_apply::<T>(ex, q, r);
    };
}

/// Introduce `□` to both sides of `⊧`.
/// 
/// ## Preconditions  
/// - `p ⊧ q`  
/// ## Postconditions  
/// - `□p ⊧ □q`
pub broadcast proof fn entails_preserved_by_always<T>(p: TempPred<T>, q: TempPred<T>)
    requires
        p.entails(q),
    ensures
        #[trigger] always(p).entails(always(q)),
{
    broadcast use always_unfold;

    assert forall|ex| always(p).satisfied_by(ex) implies always(q).satisfied_by(ex) by {
        assert forall|i: nat| q.satisfied_by(#[trigger] ex.suffix(i)) by {
            implies_apply::<T>(ex.suffix(i), p, q);
        };
    };
}

/// If `⊧ □p`, then `⊧ p`.
/// 
/// ## Preconditions  
/// - `spec ⊧ □p`
/// ## Postconditions  
/// - `spec ⊧ p`
pub proof fn eliminate_always<T>(spec: TempPred<T>, p: TempPred<T>)
    requires
        spec.entails(always(p)),
    ensures
        spec.entails(p),
{
    assert forall|ex| spec.satisfied_by(ex) implies #[trigger] p.satisfied_by(ex) by {
        implies_apply(ex, spec, always(p));
        assert(ex == ex.suffix(0));
    }
}

/// If `⊧ □(p ⇒ q)`, then `⊧ p ⇝ q`.
/// 
/// ## Preconditions    
/// - `spec ⊧ □(p ⇒ q)`
/// ## Postconditions  
/// - `spec ⊧ p ⇝ q`
pub broadcast proof fn always_implies_to_leads_to<T>(
    spec: TempPred<T>,
    p: TempPred<T>,
    q: TempPred<T>,
)
    requires
        #[trigger] spec.entails(always(p.implies(q))),
    ensures
        spec.entails(p.leads_to(q)),
{
    broadcast use {always_unfold, implies_apply, group_definition_basics};

    assert forall|ex| spec.satisfied_by(ex) implies #[trigger] p.leads_to(q).satisfied_by(ex) by {
        implies_apply(ex, spec, always(p.implies(q)));
        assert forall|i: nat| p.satisfied_by(#[trigger] ex.suffix(i)) implies eventually(
            q,
        ).satisfied_by(ex.suffix(i)) by {
            assert(ex.suffix(i) == ex.suffix(i).suffix(0));
        };
    };
}

/// If entails `□p`, then entails `□(later(p))`.
/// 
/// ## Preconditions  
/// - `spec ⊧ □p`
/// ## Postconditions  
/// - `spec ⊧ □p'`
pub broadcast proof fn always_to_always_later<T>(spec: TempPred<T>, p: TempPred<T>)
    requires
        spec.entails(always(p)),
    ensures
        #[trigger] spec.entails(always(later(p))),
{
    broadcast use {always_unfold, group_execution_suffix_lemmas};

    entails_trans(spec, always(p), always(later(p)));
}

/// If `spec1 ⊧ p` and `spec2 ⊧ q`, then `spec1 ∧ spec2 ⊧ p ∧ q`.
/// 
/// ## Preconditions  
/// - `spec1 ⊧ p`  
/// - `spec2 ⊧ q`
/// ## Postconditions    
/// - `spec1 ∧ spec2 ⊧ p ∧ q`
pub broadcast proof fn entails_and_different_temp<T>(
    spec1: TempPred<T>,
    spec2: TempPred<T>,
    p: TempPred<T>,
    q: TempPred<T>,
)
    requires
        spec1.entails(p),
        spec2.entails(q),
    ensures
        #[trigger] spec1.and(spec2).entails(p.and(q)),
{
    assert forall|ex| #[trigger] spec1.and(spec2).satisfied_by(ex) implies p.and(q).satisfied_by(
        ex,
    ) by {
        implies_apply::<T>(ex, spec1, p);
        implies_apply::<T>(ex, spec2, q);
    };
}

/// If `p ⇒ q` for all executions, then `p ⇝ q`.
/// 
/// ## Preconditions  
/// - `p ⊧ q`
/// ## Postconditions    
/// - `spec ⊧ p ⇝ q`
/// 
/// NOTE: there is no constraint on `spec`, it can be true_pred().
pub proof fn entails_implies_leads_to<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        p.entails(q),
    ensures
        spec.entails(p.leads_to(q)),
{
    valid_p_implies_always_p(p.implies(q));
    always_implies_to_leads_to(spec, p, q);
}

/// Weaken `□` by `⇒`.
/// 
/// ## Preconditions  
/// - `⊧ p ⇒ q`  
/// - `spec ⊧ □p` 
/// ## Postconditions    
/// - `spec ⊧ □q`
pub proof fn always_weaken<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        valid(p.implies(q)),
        spec.entails(always(p)),
    ensures
        spec.entails(always(q)),
{
    entails_preserved_by_always::<T>(p, q);
    assert forall|ex| #[trigger] spec.satisfied_by(ex) implies always(q).satisfied_by(ex) by {
        implies_apply::<T>(ex, spec, always(p));
        implies_apply::<T>(ex, always(p), always(q));
    };
}

/// If `⊧ p` and `⊧ p ⇝ q`, then `⊧ ◊q`.
/// 
/// ## Preconditions  
/// - `spec ⊧ p`  
/// - `spec ⊧ p ⇝ q`
/// ## Postconditions    
/// - `spec ⊧ ◊q`
pub broadcast proof fn leads_to_apply<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec.entails(p),
        #[trigger] spec.entails(p.leads_to(q)),
    ensures
        spec.entails(eventually(q)),
{
    assert forall|ex| #[trigger] spec.satisfied_by(ex) implies eventually(q).satisfied_by(ex) by {
        implies_apply::<T>(ex, spec, p);
        implies_apply::<T>(ex, spec, p.leads_to(q));
        leads_to_unfold::<T>(ex, p, q);
        assert(ex == ex.suffix(0));
        implies_apply::<T>(ex, p, eventually(q));
    };
}

/// Leads to is transitive.
/// 
/// ## Preconditions  
/// - `spec ⊧ p ⇝ q`    
/// - `spec ⊧ q ⇝ r`
/// ## Postconditions  
/// - `spec ⊧ p ⇝ r`
pub proof fn leads_to_trans<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        spec.entails(p.leads_to(q)),
        spec.entails(q.leads_to(r)),
    ensures
        spec.entails(p.leads_to(r)),
{
    broadcast use group_definition_basics;

    assert forall|ex| #[trigger] spec.satisfied_by(ex) implies p.leads_to(r).satisfied_by(ex) by {
        assert forall|i: nat| #[trigger] p.satisfied_by(ex.suffix(i)) implies eventually(
            r,
        ).satisfied_by(ex.suffix(i)) by {
            entails_apply(ex, spec, p.leads_to(q));
            always_unfold(ex, p.implies(eventually(q)));
            implies_apply(ex.suffix(i), p, eventually(q));
            eventually_unfold(ex.suffix(i), q);
            let q_witness_idx = eventually_choose_witness(ex.suffix(i), q);

            assert(ex.suffix(i + q_witness_idx) == ex.suffix(i).suffix(q_witness_idx));

            entails_apply(ex, spec, q.leads_to(r));
            always_unfold(ex, q.implies(eventually(r)));
            implies_apply(ex.suffix(i + q_witness_idx), q, eventually(r));

            eventually_propagate_backwards(ex.suffix(i), r, q_witness_idx);
        }
    };
}

/// Weaken `□` lifted state predicate by `⇒`.
/// 
/// ## Preconditions  
/// - `∀ s. p(s) ⇒ q(s)`  
/// - `spec ⊧ □lift_state(p)`
/// 
/// ## Postconditions  
/// - `spec ⊧ □lift_state(q)`
pub proof fn always_lift_state_weaken<T>(spec: TempPred<T>, p: StatePred<T>, q: StatePred<T>)
    requires
        forall|s: T| #[trigger] p.apply(s) ==> q.apply(s),
        spec.entails(always(lift_state(p))),
    ensures
        spec.entails(always(lift_state(q))),
{
    always_weaken::<T>(spec, lift_state(p), lift_state(q));
}

/// Introduce `□` to both sides of `⇒`.
/// 
/// ## Preconditions  
/// - `spec ⊧ □(p ⇒ q)`  
/// ## Postconditions  
/// - `spec ⊧ □(□p ⇒ □q)`
pub proof fn always_implies_preserved_by_always<T>(
    spec: TempPred<T>,
    p: TempPred<T>,
    q: TempPred<T>,
)
    requires
        spec.entails(always(p.implies(q))),
    ensures
        spec.entails(always(always(p).implies(always(q)))),
{
    broadcast use group_tla_rules;

    assert forall|ex| #[trigger] spec.satisfied_by(ex) implies always(
        always(p).implies(always(q)),
    ).satisfied_by(ex) by {
        assert forall|i| #[trigger] always(p).satisfied_by(ex.suffix(i)) implies always(
            q,
        ).satisfied_by(ex.suffix(i)) by {
            assert forall|j| #[trigger] q.satisfied_by(ex.suffix(i).suffix(j)) by {
                implies_apply::<T>(ex, spec, always(p.implies(q)));
                assert(ex.suffix(i + j) == ex.suffix(i).suffix(j));
                implies_apply::<T>(ex.suffix(i).suffix(j), p, q);
            };
        };
    };
}

/// Combine the premises of two `⇝` using `∨`.
/// 
/// ## Preconditions  
///  - `spec ⊧ p ⇝ r`  
///  - `spec ⊧ q ⇝ r`
/// ## Postconditions  
///  - `spec ⊧ (p ∨ q) ⇝ r`
pub broadcast proof fn or_leads_to_combine<T>(
    spec: TempPred<T>,
    p: TempPred<T>,
    q: TempPred<T>,
    r: TempPred<T>,
)
    requires
        spec.entails(p.leads_to(r)),
        spec.entails(q.leads_to(r)),
    ensures
        #[trigger] spec.entails(p.or(q).leads_to(r)),
{
    assert forall|ex| #[trigger] spec.satisfied_by(ex) implies p.or(q).leads_to(r).satisfied_by(
        ex,
    ) by {
        assert forall|i| #[trigger] p.or(q).satisfied_by(ex.suffix(i)) implies eventually(
            r,
        ).satisfied_by(ex.suffix(i)) by {
            implies_apply::<T>(ex, spec, p.leads_to(r));
            implies_apply::<T>(ex, spec, q.leads_to(r));
            leads_to_unfold::<T>(ex, p, r);
            leads_to_unfold::<T>(ex, q, r);
        };
    };
}

/// Prove `p ⇝ r` by case analysis on `q`.
/// 
/// ## Preconditions  
///  - `spec ⊧ (p ∧ q) ⇝ r`  
///  - `spec ⊧ (p ∧ ~q) ⇝ r`  
/// ## Postconditions  
///  - `spec ⊧ p ⇝ r`
pub proof fn or_leads_to_case_analysis<T>(
    spec: TempPred<T>,
    p: TempPred<T>,
    q: TempPred<T>,
    r: TempPred<T>,
)
    requires
        spec.entails(p.and(q).leads_to(r)),
        spec.entails(p.and(not(q)).leads_to(r)),
    ensures
        spec.entails(p.leads_to(r)),
{
    broadcast use group_definition_basics;

    assert forall|ex| #[trigger] spec.satisfied_by(ex) implies p.leads_to(r).satisfied_by(ex) by {
        if spec.satisfied_by(ex) {
            assert(spec.implies(p.and(q).leads_to(r)).satisfied_by(ex));
            assert(spec.implies(p.and(not(q)).leads_to(r)).satisfied_by(ex));

            leads_to_unfold(ex, p.and(q), r);
            leads_to_unfold(ex, p.and(not(q)), r);

            assert forall|i| p.implies(eventually(r)).satisfied_by(#[trigger] ex.suffix(i)) by {}
        }
    }
}

/// Combine the conclusions of two `⇝` if the conclusions are stable.
/// 
/// ## Preconditions  
///  - `spec ⊧ p ⇝ □q`  
///  - `spec ⊧ p ⇝ □r`
/// ## Postconditions  
/// - `spec ⊧ p ⇝ □(q ∧ r)`
pub broadcast proof fn leads_to_always_combine<T>(
    spec: TempPred<T>,
    p: TempPred<T>,
    q: TempPred<T>,
    r: TempPred<T>,
)
    requires
        spec.entails(p.leads_to(always(q))),
        spec.entails(p.leads_to(always(r))),
    ensures
        #![trigger spec.entails(p.leads_to(always(q).and(always(r))))]
        #![trigger spec.entails(p.leads_to(always(q.and(r))))]
        spec.entails(p.leads_to(always(q.and(r)))),
        spec.entails(p.leads_to(always(q).and(always(r)))),
{
    broadcast use group_definition_basics;

    assert forall|ex| #[trigger] spec.satisfied_by(ex) implies p.leads_to(
        always(q.and(r)),
    ).satisfied_by(ex) by {
        assert forall|i| #[trigger] p.satisfied_by(ex.suffix(i)) implies eventually(
            always(q.and(r)),
        ).satisfied_by(ex.suffix(i)) by {
            implies_apply::<T>(ex, spec, p.leads_to(always(q)));
            implies_apply::<T>(ex, spec, p.leads_to(always(r)));

            implies_apply::<T>(ex.suffix(i), p, eventually(always(q)));
            implies_apply::<T>(ex.suffix(i), p, eventually(always(r)));

            let witness_q_idx = eventually_choose_witness::<T>(ex.suffix(i), always(q));
            let witness_r_idx = eventually_choose_witness::<T>(ex.suffix(i), always(r));

            if witness_q_idx < witness_r_idx {
                always_propagate_forwards::<T>(
                    ex.suffix(i).suffix(witness_q_idx),
                    q,
                    (witness_r_idx - witness_q_idx) as nat,
                );
                assert(ex.suffix(i).suffix(witness_r_idx) == ex.suffix(i).suffix(
                    witness_q_idx,
                ).suffix((witness_r_idx - witness_q_idx) as nat));
                eventually_proved_by_witness(ex.suffix(i), always(q.and(r)), witness_r_idx);
            } else {
                always_propagate_forwards::<T>(
                    ex.suffix(i).suffix(witness_r_idx),
                    r,
                    (witness_q_idx - witness_r_idx) as nat,
                );
                assert(ex.suffix(i).suffix(witness_q_idx) == ex.suffix(i).suffix(
                    witness_r_idx,
                ).suffix((witness_q_idx - witness_r_idx) as nat));
                eventually_proved_by_witness(ex.suffix(i), always(q.and(r)), witness_q_idx);
            }
        };
    };
    always_and_equality(q, r);
}

/// Prove `p ⇝ □q` by showing that `q` is preserved.
/// 
/// ## Preconditions  
///  - `spec ⊧ □(q ∧ next ⇒ q')`  
///  - `spec ⊧ □next`  
///  - `spec ⊧ p ⇝ q`  
/// ## Postconditions
///  - `spec ⊧ p ⇝ □q`
pub proof fn leads_to_stable<T>(
    spec: TempPred<T>,
    next: TempPred<T>,
    p: TempPred<T>,
    q: TempPred<T>,
)
    requires
        spec.entails(always(q.and(next).implies(later(q)))),
        spec.entails(always(next)),
        spec.entails(p.leads_to(q)),
    ensures
        spec.entails(p.leads_to(always(q))),
{
    broadcast use {always_unfold, always_propagate_forwards, group_definition_basics};

    assert forall|ex| #[trigger] spec.satisfied_by(ex) implies p.leads_to(always(q)).satisfied_by(
        ex,
    ) by {
        assert forall|i| #[trigger] p.satisfied_by(ex.suffix(i)) implies eventually(
            always(q),
        ).satisfied_by(ex.suffix(i)) by {
            implies_apply::<T>(ex, spec, p.leads_to(q));
            leads_to_unfold::<T>(ex, p, q);
            implies_apply::<T>(ex.suffix(i), p, eventually(q));
            let witness_idx = eventually_choose_witness::<T>(ex.suffix(i), q);

            implies_apply::<T>(ex, spec, always(q.and(next).implies(later(q))));
            always_propagate_forwards::<T>(
                ex.suffix(i),
                q.and(next).implies(later(q)),
                witness_idx,
            );

            implies_apply::<T>(ex, spec, always(next));
            always_propagate_forwards::<T>(ex.suffix(i), next, witness_idx);

            assert forall|j| #[trigger]
                q.satisfied_by(ex.suffix(i).suffix(witness_idx).suffix(j)) by {
                assert forall|idx|
                    q.satisfied_by(#[trigger] ex.suffix(i).suffix(witness_idx).suffix(idx))
                        && next.satisfied_by(
                        ex.suffix(i).suffix(witness_idx).suffix(idx),
                    ) implies q.satisfied_by(ex.suffix(i).suffix(witness_idx).suffix(idx + 1)) by {
                    implies_apply::<T>(
                        ex.suffix(i).suffix(witness_idx).suffix(idx),
                        q.and(next),
                        later(q),
                    );
                    assert(ex.suffix(i).suffix(witness_idx).suffix(idx + 1) == ex.suffix(i).suffix(
                        witness_idx,
                    ).suffix(idx).suffix(1));
                };
                next_preserves_inv_rec::<T>(ex.suffix(i).suffix(witness_idx), next, q, j);
            };

            eventually_proved_by_witness::<T>(ex.suffix(i), always(q), witness_idx);
        };
    };
}

/// Sandwich `⇝` with `∨ r`.
/// 
/// ## Preconditions  
/// - `spec ⊧ p ⇝ q`
/// ## Postconditions  
/// - `spec ⊧ p ∨ r ⇝ q ∨ r`
pub broadcast proof fn leads_to_framed_by_or<T>(
    spec: TempPred<T>,
    p: TempPred<T>,
    q: TempPred<T>,
    r: TempPred<T>,
)
    requires
        spec.entails(p.leads_to(q)),
    ensures
        #[trigger] spec.entails(p.or(r).leads_to(q.or(r))),
{
    broadcast use {implies_apply, group_execution_suffix_lemmas, group_definition_basics};

    assert forall|ex| #[trigger] spec.satisfied_by(ex) implies p.or(r).leads_to(
        q.or(r),
    ).satisfied_by(ex) by {
        assert forall|i| #[trigger] p.or(r).satisfied_by(ex.suffix(i)) implies eventually(
            q.or(r),
        ).satisfied_by(ex.suffix(i)) by {
            implies_apply(ex, spec, p.leads_to(q));
            leads_to_unfold(ex, p, q);
            if p.satisfied_by(ex.suffix(i)) {
                let witness_idx = eventually_choose_witness(ex.suffix(i), q);
                eventually_proved_by_witness(ex.suffix(i), q.or(r), witness_idx);
            } else {
                let witness_idx = 0;
                eventually_proved_by_witness(ex.suffix(i), q.or(r), witness_idx);
            }
        }
    }
}

/// Combine two `⇝` with a shortcut.
/// 
/// ## Preconditions  
/// - `spec ⊧ p ⇝ q ∨ s`  
/// - `spec ⊧ q ⇝ r ∨ s`
/// ## Postconditions  
/// - `spec ⊧ p ⇝ r ∨ s`
pub proof fn leads_to_shortcut_temp<T>(
    spec: TempPred<T>,
    p: TempPred<T>,
    q: TempPred<T>,
    r: TempPred<T>,
    s: TempPred<T>,
)
    requires
        spec.entails(p.leads_to(q.or(s))),
        spec.entails(q.leads_to(r.or(s))),
    ensures
        spec.entails(p.leads_to(r.or(s))),
{
    leads_to_framed_by_or(spec, q, r.or(s), s);
    temp_pred_equality(r.or(s).or(s), r.or(s));
    leads_to_trans(spec, p, q.or(s), r.or(s));
}

/// If `⊧ □(lift_state(p))` and `⊧ □(lift_state(q))`, then `⊧ □(lift_state(p ∧ q))`.
/// 
/// ## Preconditions  
///  - `spec ⊧ □lift_state(p)`  
///  - `spec ⊧ □lift_state(q)`
/// ## Postconditions  
///  - `spec ⊧ □lift_state(p ∧ q)`
pub broadcast proof fn entails_always_lift_state_and<T>(
    spec: TempPred<T>,
    p: StatePred<T>,
    q: StatePred<T>,
)
    requires
        spec.entails(always(lift_state(p))),
        spec.entails(always(lift_state(q))),
    ensures
        #[trigger] spec.entails(always(lift_state(p.and(q)))),
{
    broadcast use group_definition_basics;

}

/// Eliminate and split two state predicates under `□`.
///
/// ## Preconditions  
/// - `spec ⊧ □lift_state(p ∧ q)`
/// ## Postconditions  
/// - `spec ⊧ □lift_state(p)`  
/// - `spec ⊧ □lift_state(q)`
pub broadcast proof fn entails_always_lift_state_and_elim<T>(
    spec: TempPred<T>,
    p: StatePred<T>,
    q: StatePred<T>,
)
    requires
        #[trigger] spec.entails(always(lift_state(p.and(q)))),
    ensures
        spec.entails(always(lift_state(p))),
        spec.entails(always(lift_state(q))),
{
    broadcast use group_definition_basics;

}

// Rules about quantifiers.
/// Lift the `exists` outside `lift_state`.
/// 
/// ## Postconditions  
/// - `lift_state(∃ a: A. p(a)) == ∃ a: A. lift_state(p(a))`
pub broadcast proof fn lift_state_exists_equality<T, A>(a_to_state_pred: spec_fn(A) -> StatePred<T>)
    ensures
        #[trigger] lift_state_exists(a_to_state_pred) == tla_exists(
            |a| lift_state(a_to_state_pred(a)),
        ),
{
    let p = lift_state_exists(a_to_state_pred);
    let q = tla_exists(|a| lift_state(a_to_state_pred(a)));
    let partial_p = |t| exists|a| #[trigger] a_to_state_pred(a).apply(t);
    let partial_q = |a| lift_state(a_to_state_pred(a));
    assert forall|ex| p.satisfied_by(ex) implies q.satisfied_by(ex) by {
        assert(exists|a| #[trigger] a_to_state_pred(a).apply(ex.head()));
        let witness_a = choose|a| #[trigger] a_to_state_pred(a).apply(ex.head());
        assert(partial_q(witness_a).satisfied_by(ex));
    };

    temp_pred_equality::<T>(p, q);
}

/// Lift the `□` outside `tla_forall` if the function is previously wrapped by an `□`.
/// 
/// ## Postconditions  
/// - `∀ a:A. □P(a) == □(∀ a:A. P(a)))`
/// 
/// NOTE: Verus may not able to infer that `(|a| func(a))(a)` equals `func(a)`.
///       Please turn to lemma [`tla_forall_always_equality_variant`] for troubleshooting.
pub proof fn tla_forall_always_equality<T, A>(a_to_temp_pred: spec_fn(A) -> TempPred<T>)
    ensures
        tla_forall(|a: A| always(a_to_temp_pred(a))) == always(tla_forall(a_to_temp_pred)),
{
    broadcast use {always_unfold, tla_forall_unfold};

    let a_to_always_p = |a: A| always(a_to_temp_pred(a));

    assert forall|ex| #[trigger] tla_forall(a_to_always_p).satisfied_by(ex) implies always(
        tla_forall(a_to_temp_pred),
    ).satisfied_by(ex) by {
        assert forall|i| #[trigger] tla_forall(a_to_temp_pred).satisfied_by(ex.suffix(i)) by {
            assert forall|a| #[trigger] a_to_temp_pred(a).satisfied_by(ex.suffix(i)) by {
                assert(a_to_always_p(a).satisfied_by(ex));
            };
        };
    };

    temp_pred_equality::<T>(
        tla_forall(|a: A| always(a_to_temp_pred(a))),
        always(tla_forall(a_to_temp_pred)),
    );
}

pub proof fn tla_forall_always_equality_variant<T, A>(
    a_to_always: spec_fn(A) -> TempPred<T>,
    a_to_temp_pred: spec_fn(A) -> TempPred<T>,
)
    requires
        forall|a: A|
            #![trigger a_to_always(a)]
            a_to_always(a).entails((|a: A| always(a_to_temp_pred(a)))(a)) && ((|a: A|
                always(a_to_temp_pred(a)))(a)).entails(a_to_always(a)),
    ensures
        tla_forall(a_to_always) == always(tla_forall(a_to_temp_pred)),
{
    a_to_temp_pred_equality::<T, A>(a_to_always, |a: A| always(a_to_temp_pred(a)));
    temp_pred_equality::<T>(tla_forall(a_to_always), tla_forall(|a: A| always(a_to_temp_pred(a))));
    tla_forall_always_equality::<T, A>(a_to_temp_pred);
}

/// If `forall a. P(a)` holds, then `P` holds for any particular `a`.
/// 
/// ## Postconditions  
/// - `∀ a: A. P(a) ⊧ P(a)`
pub broadcast proof fn tla_forall_apply<T, A>(a_to_temp_pred: spec_fn(A) -> TempPred<T>, a: A)
    ensures
        #[trigger] tla_forall(a_to_temp_pred).entails(a_to_temp_pred(a)),
{
    broadcast use tla_forall_unfold;

}

// Used to be named as always_tla_forall_apply
/// If `⊧ □(∀ a. P(a))`, then `⊧ □(P(a))` for any particular `a`.
/// 
/// ## Preconditions  
/// - `spec ⊧ □(∀ a: A. P(a))`
/// ## Postconditions  
/// - `spec ⊧ □(P(a))`
pub proof fn use_always_tla_forall<T, A>(
    spec: TempPred<T>,
    a_to_temp_pred: spec_fn(A) -> TempPred<T>,
    a: A,
)
    requires
        spec.entails(always(tla_forall(a_to_temp_pred))),
    ensures
        spec.entails(always(a_to_temp_pred(a))),
{
    entails_preserved_by_always(tla_forall(a_to_temp_pred), a_to_temp_pred(a));
    entails_trans(spec, always(tla_forall(a_to_temp_pred)), always(a_to_temp_pred(a)));
}

/// If ⊧ `P(a)` for all `a`, then ⊧ `∀ a. P(a)`.
/// 
/// ## Preconditions  
/// - `forall a: A. spec ⊧ P(a)`
/// 
/// ## Postconditions  
/// - `spec ⊧ ∀ a: A. P(a)`
pub broadcast proof fn spec_entails_tla_forall<T, A>(
    spec: TempPred<T>,
    a_to_temp_pred: spec_fn(A) -> TempPred<T>,
)
    requires
        forall|a: A| spec.entails(#[trigger] a_to_temp_pred(a)),
    ensures
        #[trigger] spec.entails(tla_forall(a_to_temp_pred)),
{
    assert forall|ex| #[trigger] spec.satisfied_by(ex) implies tla_forall(
        a_to_temp_pred,
    ).satisfied_by(ex) by {
        assert forall|a| #[trigger] a_to_temp_pred(a).satisfied_by(ex) by {
            implies_apply::<T>(ex, spec, a_to_temp_pred(a));
        };
    };
}

/// If ⊧ `□(P(a))` for all `a`, then ⊧ `□(∀ a. P(a))`.
/// 
/// ## Preconditions  
/// - `forall a: A. spec ⊧ □P(a)`
/// ## Postconditions  
/// - `spec ⊧ □(∀ a: A. P(a))`
pub proof fn spec_entails_always_tla_forall<T, A>(
    spec: TempPred<T>,
    a_to_temp_pred: spec_fn(A) -> TempPred<T>,
)
    requires
        forall|a: A| spec.entails(always(#[trigger] a_to_temp_pred(a))),
    ensures
        spec.entails(always(tla_forall(a_to_temp_pred))),
{
    let a_to_always = |a: A| always(a_to_temp_pred(a));
    spec_entails_tla_forall(spec, a_to_always);
    tla_forall_always_equality_variant::<T, A>(a_to_always, a_to_temp_pred);
}

/// If ⊧ `□(p ⇒ P(a))` for all `a`, then ⊧ `□(p ⇒ forall a. P(a))`.
/// 
/// ## Preconditions  
///  - `forall a: A. spec ⊧ □(p ⇒ P(a))`
/// ## Postconditions  
///  - `spec ⊧ □(p ⇒ (∀ a: A. P(a)))`
pub broadcast proof fn always_implies_forall_intro<T, A>(
    spec: TempPred<T>,
    p: TempPred<T>,
    a_to_temp_pred: spec_fn(A) -> TempPred<T>,
)
    requires
        forall|a: A| #[trigger] spec.entails(always(p.implies(a_to_temp_pred(a)))),
    ensures
        #[trigger] spec.entails(always(p.implies(tla_forall(a_to_temp_pred)))),
{
    let a_to_always_p_implies_q = |a: A| always(p.implies(a_to_temp_pred(a)));
    spec_entails_tla_forall::<T, A>(spec, a_to_always_p_implies_q);
    assert forall|ex| #[trigger] spec.satisfied_by(ex) implies always(
        p.implies(tla_forall(a_to_temp_pred)),
    ).satisfied_by(ex) by {
        implies_apply::<T>(ex, spec, tla_forall(a_to_always_p_implies_q));
        tla_forall_always_implies_equality2::<T, A>(p, a_to_temp_pred)
    };
}

/// If ⊧ `P(a) ⇝ q` for all `a`, then ⊧ `exists a. P(a) leads_to q`.
/// 
/// ## Preconditions  
///  - `forall a: A. spec ⊧ P(a) ⇝ q`
/// ## Postconditions  
///  - `spec ⊧ (∃ a: A. P(a)) ⇝ q`
pub broadcast proof fn tla_exists_leads_to_intro<T, A>(
    spec: TempPred<T>,
    a_to_temp_pred: spec_fn(A) -> TempPred<T>,
    q: TempPred<T>,
)
    requires
        forall|a: A| #[trigger] spec.entails(a_to_temp_pred(a).leads_to(q)),
    ensures
        #[trigger] spec.entails(tla_exists(a_to_temp_pred).leads_to(q)),
{
    let a_to_temp_pred_leads_to_q = |a: A| a_to_temp_pred(a).leads_to(q);
    spec_entails_tla_forall::<T, A>(spec, a_to_temp_pred_leads_to_q);
    assert forall|ex| #[trigger] spec.satisfied_by(ex) implies tla_exists(a_to_temp_pred).leads_to(
        q,
    ).satisfied_by(ex) by {
        implies_apply::<T>(ex, spec, tla_forall(a_to_temp_pred_leads_to_q));
        tla_forall_leads_to_equality1::<T, A>(a_to_temp_pred, q);
    };
}

/// If ⊧ `forall a. P(a)`, then ⊧ `P(a)` for any particular `a`.
/// 
/// ## Preconditions  
///  - `spec ⊧ (∀ a: A. P(a))`
/// ## Postconditions  
///  - `spec ⊧ P(a)`
pub proof fn use_tla_forall<T, A>(
    spec: TempPred<T>,
    a_to_temp_pred: spec_fn(A) -> TempPred<T>,
    a: A,
)
    requires
        spec.entails(tla_forall(a_to_temp_pred)),
    ensures
        spec.entails(a_to_temp_pred(a)),
{
    assert forall|ex: Execution<T>| #[trigger] spec.satisfied_by(ex) implies (a_to_temp_pred(
        a,
    )).satisfied_by(ex) by {
        entails_apply(ex, spec, tla_forall(a_to_temp_pred));
        assert(spec.implies(tla_forall(a_to_temp_pred)).satisfied_by(ex));
    };
}

pub broadcast proof fn entails_tla_exists_by_witness<T, A>(
    spec: TempPred<T>,
    p: spec_fn(A) -> TempPred<T>,
    a: A,
)
    requires
        #[trigger] spec.entails(p(a)),
    ensures
        spec.entails(tla_exists(p)),
{
    assert forall|ex| #[trigger] spec.satisfied_by(ex) implies tla_exists(p).satisfied_by(ex) by {
        implies_apply::<T>(ex, spec, p(a));
        tla_exists_unfold::<T, A>(ex, p);
    };
}

pub proof fn implies_tla_exists_by_witness<T, A>(
    spec: TempPred<T>,
    p: TempPred<T>,
    q: spec_fn(A) -> TempPred<T>,
    a: A,
)
    requires
        spec.entails(p.implies(q(a))),
    ensures
        spec.entails(p.implies(tla_exists(q))),
{
    assert forall|ex| #[trigger] spec.satisfied_by(ex) implies p.implies(
        tla_exists(q),
    ).satisfied_by(ex) by {
        implies_apply(ex, spec, p.implies(q(a)));
    };
}

pub broadcast proof fn implies_tla_exists_intro<T, A>(
    spec: TempPred<T>,
    p: TempPred<T>,
    q: spec_fn(A) -> TempPred<T>,
)
    requires
        exists|a: A| #[trigger] spec.entails(p.implies(q(a))),
    ensures
        #[trigger] spec.entails(p.implies(tla_exists(q))),
{
    let witness = choose|a: A| #[trigger] spec.entails(p.implies(q(a)));
    implies_tla_exists_by_witness(spec, p, q, witness);
}

pub proof fn leads_to_tla_exists_by_witness<T, A>(
    spec: TempPred<T>,
    p: TempPred<T>,
    q: spec_fn(A) -> TempPred<T>,
    a: A,
)
    requires
        spec.entails(p.leads_to(q(a))),
    ensures
        spec.entails(p.leads_to(tla_exists(q))),
{
    assert forall|ex| #[trigger] always(q(a).implies(tla_exists(q))).satisfied_by(ex) by {
        assert forall|i: nat| q(a).implies(tla_exists(q)).satisfied_by(ex.suffix(i)) by {
            if q(a).satisfied_by(ex.suffix(i)) {
                tla_exists_proved_by_witness(ex.suffix(i), q, a);
            }
        };
    };
    leads_to_weaken(spec, p, q(a), p, tla_exists(q));
}

pub broadcast proof fn leads_to_tla_exists_intro<T, A>(
    spec: TempPred<T>,
    p: TempPred<T>,
    q: spec_fn(A) -> TempPred<T>,
)
    requires
        exists|a: A| #[trigger] spec.entails(p.leads_to(q(a))),
    ensures
        #[trigger] spec.entails(p.leads_to(tla_exists(q))),
{
    let witness = choose|a: A| #[trigger] spec.entails(p.leads_to(q(a)));
    leads_to_tla_exists_by_witness(spec, p, q, witness);
}

pub broadcast proof fn lift_state_exists_leads_to_intro<T, A>(
    spec: TempPred<T>,
    a_to_temp_pred: spec_fn(A) -> StatePred<T>,
    q: TempPred<T>,
)
    requires
        forall|a: A| #[trigger] spec.entails(lift_state(a_to_temp_pred(a)).leads_to(q)),
    ensures
        #[trigger] spec.entails(lift_state_exists(a_to_temp_pred).leads_to(q)),
{
    lift_state_exists_equality(a_to_temp_pred);
    let lifted_a_to_temp_pred = |a: A| lift_state(a_to_temp_pred(a));
    tla_exists_leads_to_intro(spec, lifted_a_to_temp_pred, q);
}

pub broadcast proof fn state_exists_intro<T, A>(a_to_temp_pred: spec_fn(A) -> StatePred<T>, s: T)
    requires
        exists|a: A| #[trigger] a_to_temp_pred(a).apply(s),
    ensures
        #[trigger] StatePred::state_exists(a_to_temp_pred).apply(s),
{
}

pub broadcast proof fn lift_state_exists_absorb_equality<T, A>(
    a_to_state_pred: spec_fn(A) -> StatePred<T>,
    state_pred: StatePred<T>,
)
    ensures
        #[trigger] lift_state_exists(a_to_state_pred).and(lift_state(state_pred))
            == lift_state_exists(StatePred::absorb(a_to_state_pred, state_pred)),
{
    broadcast use group_definition_basics;

    let lhs = lift_state_exists(a_to_state_pred).and(lift_state(state_pred));
    let rhs = lift_state_exists(StatePred::absorb(a_to_state_pred, state_pred));

    assert forall|ex| lhs.satisfied_by(ex) == rhs.satisfied_by(ex) by {
        let s = ex.head();

        if lhs.satisfied_by(ex) {
            let a = choose|a| #[trigger] a_to_state_pred(a).apply(s);
            assert(StatePred::absorb(a_to_state_pred, state_pred)(a).apply(s));
        }
        if rhs.satisfied_by(ex) {
            let a = choose|a| #[trigger] StatePred::absorb(a_to_state_pred, state_pred)(a).apply(s);
        }
    }
    temp_pred_equality(lhs, rhs);
}

pub broadcast proof fn lift_state_forall_absorb_equality<T, A>(
    a_to_state_pred: spec_fn(A) -> StatePred<T>,
    state_pred: StatePred<T>,
)
    requires
        Set::<A>::full() != Set::<A>::empty(),
    ensures
        #[trigger] lift_state_forall(a_to_state_pred).and(lift_state(state_pred))
            == lift_state_forall(StatePred::absorb(a_to_state_pred, state_pred)),
{
    broadcast use group_definition_basics;

    let lhs = lift_state_forall(a_to_state_pred).and(lift_state(state_pred));
    let rhs = lift_state_forall(StatePred::absorb(a_to_state_pred, state_pred));

    assert forall|ex| lhs.satisfied_by(ex) == rhs.satisfied_by(ex) by {
        let s = ex.head();

        if lhs.satisfied_by(ex) {
            assert forall|a| #[trigger]
                StatePred::absorb(a_to_state_pred, state_pred)(a).apply(s) by {}
        }
        if rhs.satisfied_by(ex) {
            let a = choose|a| Set::<A>::full().contains(a);
            assert(StatePred::absorb(a_to_state_pred, state_pred)(a).apply(s));
            assert forall|a| #[trigger] a_to_state_pred(a).apply(s) by {
                assert(StatePred::absorb(a_to_state_pred, state_pred)(a).apply(s));
            }
        }
    }
    temp_pred_equality(lhs, rhs);
}

/// Prove `lift_state_exists` leads to by case analysis on another `StatePred`.
/// 
/// ## Preconditions  
/// - `spec ⊧ lift_state_exists(absorb(a_to_temp_pred, p)) ⇝ q`  
/// - `spec ⊧ lift_state_exists(absorb(a_to_temp_pred, ~p)) ⇝ q`
/// ## Postconditions  
/// - `spec ⊧ lift_state_exists(a_to_temp_pred) ⇝ q`
pub proof fn lift_state_exists_leads_to_case_analysis<T, A>(
    spec: TempPred<T>,
    a_to_temp_pred: spec_fn(A) -> StatePred<T>,
    p: StatePred<T>,
    q: TempPred<T>,
)
    requires
        spec.entails(lift_state_exists(StatePred::absorb(a_to_temp_pred, p)).leads_to(q)),
        spec.entails(lift_state_exists(StatePred::absorb(a_to_temp_pred, p.not())).leads_to(q)),
    ensures
        spec.entails(lift_state_exists(a_to_temp_pred).leads_to(q)),
{
    broadcast use {lift_state_exists_absorb_equality, group_definition_basics};

    or_leads_to_case_analysis(spec, lift_state_exists(a_to_temp_pred), lift_state(p), q);
}

/// Leads to `□tla_forall(a_to_temp_pred)` if forall `a`, it leads to `□a_to_temp_pred(a)`.
/// 
/// ## Preconditions  
/// - `forall |a: A|, spec ⊧ p ⇝ □a_to_temp_pred(a)`  
/// - `forall |a: A|, a \in domain`  
/// - `domain.is_finite() && domain.len() > 0`  
/// ## Postconditions  
/// - `spec ⊧ □tla_forall(a_to_temp_pred)`
/// 
/// The domain set assist in showing type A contains finite elements.
//
// This lemma is actually similar to leads_to_always_combine_n when the n predicates are all a_to_temp_pred(a) for some a.
// This is because tla_forall(a_to_temp_pred) == a_to_temp_pred(a1).and(a_to_temp_pred(a2))....and(a_to_temp_pred(an)), We only consider the case when
// type A is finite here.
pub proof fn leads_to_always_tla_forall<T, A>(
    spec: TempPred<T>,
    p: TempPred<T>,
    a_to_temp_pred: spec_fn(A) -> TempPred<T>,
    domain: Set<A>,
)
    requires
        forall|a: A| spec.entails(p.leads_to(always(#[trigger] a_to_temp_pred(a)))),
        domain.finite(),
        domain.len() > 0,
        forall|a: A| #[trigger] domain.contains(a),
    ensures
        spec.entails(p.leads_to(always(tla_forall(a_to_temp_pred)))),
{
    broadcast use {always_unfold, always_propagate_forwards, group_definition_basics};

    assert forall|ex| #[trigger] spec.satisfied_by(ex) implies p.leads_to(
        always(tla_forall(a_to_temp_pred)),
    ).satisfied_by(ex) by {
        assert forall|i| #[trigger] p.satisfied_by(ex.suffix(i)) implies eventually(
            always(tla_forall(a_to_temp_pred)),
        ).satisfied_by(ex.suffix(i)) by {
            assert forall|a: A|
                p.leads_to(always(#[trigger] a_to_temp_pred(a))).satisfied_by(ex) by {
                implies_apply::<T>(ex, spec, p.leads_to(always(a_to_temp_pred(a))));
            }
            assert forall|a: A|
                eventually(always(#[trigger] a_to_temp_pred(a))).satisfied_by(ex.suffix(i)) by {
                implies_apply::<T>(ex.suffix(i), p, eventually(always(a_to_temp_pred(a))));
            }

            let a_to_witness = Map::new(
                |a: A| domain.contains(a),
                |a: A|
                    {
                        let wit = eventually_choose_witness::<T>(
                            ex.suffix(i),
                            always(a_to_temp_pred(a)),
                        );
                        wit
                    },
            );
            assert(a_to_witness.dom() == domain);
            let r = |a1: nat, a2: nat| a1 <= a2;
            let values = a_to_witness.values();
            lemma_values_finite(a_to_witness);
            assert_by(
                values.len() > 0,
                {
                    let x = a_to_witness.dom().choose();
                    assert(values.contains(a_to_witness[x]));
                },
            );
            let max_witness = values.find_unique_maximal(r);
            values.find_unique_maximal_ensures(r);
            values.lemma_maximal_equivalent_greatest(r, max_witness);

            assert forall|a: A|
                always(#[trigger] a_to_temp_pred(a)).satisfied_by(
                    ex.suffix(i).suffix(max_witness),
                ) by {
                let witness = a_to_witness[a];
                assert(r(witness, max_witness));
                assert(ex.suffix(i).suffix(max_witness) == ex.suffix(i).suffix(witness).suffix(
                    (max_witness - witness) as nat,
                ));
            }
            eventually_proved_by_witness(
                ex.suffix(i),
                always(tla_forall(a_to_temp_pred)),
                max_witness,
            );
        };
    };
}

// Rules about stability.
/// An `□` predicate is `stable`.
/// 
/// ## Postconditions  
/// - `⊧ stable(□p)`
pub broadcast proof fn always_p_is_stable<T>(p: TempPred<T>)
    ensures
        #[trigger] valid(stable(always(p))),
{
    broadcast use {always_unfold, always_propagate_forwards};

}

/// A `⇝` predicate is stable.
/// 
/// ## Postconditions  
/// - `⊧ stable(p ⇝ q)`
pub proof fn p_leads_to_q_is_stable<T>(p: TempPred<T>, q: TempPred<T>)
    ensures
        valid(stable(p.leads_to(q))),
{
    always_p_is_stable(p.implies(eventually(q)));
}

/// `p ∧ q` is stable if both `p` and `q` are stable.
/// 
/// ## Preconditions  
/// - `⊧ stable(p)`  
/// - `⊧ stable(q)`  
/// ## Postconditions  
/// - `⊧ stable(p ∧ q)`
pub broadcast proof fn stable_and_temp<T>(p: TempPred<T>, q: TempPred<T>)
    requires
        valid(stable(p)),
        valid(stable(q)),
    ensures
        #[trigger] valid(stable(p.and(q))),
{
    assert forall|ex| #[trigger] p.and(q).satisfied_by(ex) implies always(p.and(q)).satisfied_by(
        ex,
    ) by {
        stable_unfold::<T>(ex, p);
        stable_unfold::<T>(ex, q);
    }
}

/// `forall a ⇝ p -> q(a)` is stable.
/// 
/// ## Preconditions  
/// - `∀ a. ⊧ stable(p -> q(a))`  
/// 
/// ## Postconditions  
/// - `⊧ stable(∀ a. p -> q(a)))`
pub proof fn tla_forall_a_p_leads_to_q_a_is_stable<T, A>(
    p: TempPred<T>,
    a_to_temp_pred: spec_fn(A) -> TempPred<T>,
)
    requires
        forall|a: A| #[trigger] valid(stable(p.leads_to(a_to_temp_pred(a)))),
    ensures
        valid(stable(tla_forall(|a: A| p.leads_to(a_to_temp_pred(a))))),
{
    broadcast use group_definition_basics;

    let target = tla_forall(|a: A| p.leads_to(a_to_temp_pred(a)));
    assert forall|ex|
        (forall|a: A| #[trigger]
            valid(stable(p.leads_to(a_to_temp_pred(a))))) implies #[trigger] stable(
        target,
    ).satisfied_by(ex) by {
        assert forall|i|
            (forall|a: A| #[trigger] valid(stable(p.leads_to(a_to_temp_pred(a)))))
                && target.satisfied_by(ex) implies #[trigger] target.satisfied_by(ex.suffix(i)) by {
            assert forall|a: A|
                p.leads_to(a_to_temp_pred(a)).satisfied_by(ex) implies #[trigger] p.leads_to(
                a_to_temp_pred(a),
            ).satisfied_by(ex.suffix(i)) by {
                assert(valid(stable(p.leads_to(a_to_temp_pred(a)))));
                assert(stable(p.leads_to(a_to_temp_pred(a))).satisfied_by(ex));
                if p.leads_to(a_to_temp_pred(a)).satisfied_by(ex) {
                }
            }
        }
    }
}

/// Unpack the conditions from the left to the right side of `⊧`
/// 
/// ## Preconditions  
/// - `⊧ stable(spec)`  
/// - `spec ∧ c ⊧ p ⇝ q`
/// ## Postconditions  
/// - `spec ⊧ p ∧ c ⇝ q`
pub proof fn unpack_conditions_from_spec<T>(
    spec: TempPred<T>,
    c: TempPred<T>,
    p: TempPred<T>,
    q: TempPred<T>,
)
    requires
        valid(stable(spec)),
        spec.and(c).entails(p.leads_to(q)),
    ensures
        spec.entails(p.and(c).leads_to(q)),
{
    broadcast use {always_unfold, implies_apply, group_definition_basics};

    assert forall|ex| #[trigger] spec.satisfied_by(ex) implies p.and(c).leads_to(q).satisfied_by(
        ex,
    ) by {
        assert forall|i| #[trigger] p.and(c).satisfied_by(ex.suffix(i)) implies eventually(
            q,
        ).satisfied_by(ex.suffix(i)) by {
            stable_unfold::<T>(ex, spec);
            implies_apply::<T>(ex.suffix(i), spec.and(c), p.leads_to(q));
            assert(ex.suffix(i) == ex.suffix(i).suffix(0));
            implies_apply::<T>(ex.suffix(i), p, eventually(q));
        };
    };
}

/// Pack the conditions from the right to the left side of `⊧`.
/// 
/// ## Preconditions  
/// - `spec ⊧ p ∧ c ⇝ q`
/// 
/// ## Postconditions  
/// - `spec ∧ □c ⊧ p ⇝ q`
pub proof fn pack_conditions_to_spec<T>(
    spec: TempPred<T>,
    c: TempPred<T>,
    p: TempPred<T>,
    q: TempPred<T>,
)
    requires
        spec.entails(p.and(c).leads_to(q)),
    ensures
        spec.and(always(c)).entails(p.leads_to(q)),
{
    broadcast use {always_unfold, always_propagate_forwards};

    assert forall|ex| #[trigger] spec.and(always(c)).satisfied_by(ex) implies p.leads_to(
        q,
    ).satisfied_by(ex) by {
        implies_apply(ex, spec, p.and(c).leads_to(q));
        leads_to_unfold(ex, p.and(c), q);

    }
}

/// Make the predicate as concise as possible.
/// 
/// Similar to the first-order logic where `p` equals `p ∧ q` when `p -> q` is satisfied,
/// we can reduce the size of predicate when some part of it implies the rest.
///
/// ## Preconditions  
/// - `p ⊧ q`  
/// ## Postconditions  
/// - `p == p ∧ q`
// Used to be named as simplify_predicate.
pub proof fn entails_and_equality<T>(p: TempPred<T>, q: TempPred<T>)
    requires
        p.entails(q),
    ensures
        p == p.and(q),
{
    assert forall|ex| #[trigger] p.satisfied_by(ex) implies p.and(q).satisfied_by(ex) by {
        entails_and_temp::<T>(p, p, q);
        entails_apply::<T>(ex, p, p.and(q));
    };
    temp_pred_equality::<T>(p, p.and(q));
}

/// Transitivity of `⊧` with simplification.
/// 
/// ## Preconditions  
/// - `spec ⊧ p`  
/// - `spec ∧ p ⊧ q`
/// ## Postconditions  
/// - `spec ⊧ q`
pub proof fn entails_trans_by_simplify<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec.entails(p),
        spec.and(p).entails(q),
    ensures
        spec.entails(q),
{
    entails_and_equality(spec, p);
}

// More advanced rules.
/// Proving `p ⇝ q` by borrowing the inv.
/// 
/// ## Preconditions  
/// - `spec ⊧ p ∧ inv ⇝ q`  
/// - `spec ⊧ □inv`
/// ## Postconditions  
/// - `spec ⊧ p ⇝ q`
pub proof fn leads_to_by_borrowing_inv<T>(
    spec: TempPred<T>,
    p: TempPred<T>,
    q: TempPred<T>,
    inv: TempPred<T>,
)
    requires
        spec.entails(p.and(inv).leads_to(q)),
        spec.entails(always(inv)),
    ensures
        spec.entails(p.leads_to(q)),
{
    assert forall|ex| #[trigger] spec.satisfied_by(ex) implies p.leads_to(q).satisfied_by(ex) by {
        assert forall|i| #[trigger] p.satisfied_by(ex.suffix(i)) implies eventually(q).satisfied_by(
            ex.suffix(i),
        ) by {
            instantiate_entailed_always(ex, i, spec, inv);
            instantiate_entailed_leads_to(ex, i, spec, p.and(inv), q);
        }
    }
}

/// Enhance the conclusion of leads-to □ using invariant.
/// 
/// ## Preconditions  
/// - `spec ⊧ □inv`  
/// - `spec ⊧ p ⇝ □q1`  
/// - `q1 ∧ inv ⊧ q2`
/// ## Postconditions  
/// - `spec ⊧ p ⇝ □q2`
pub proof fn leads_to_always_enhance<T>(
    spec: TempPred<T>,
    inv: TempPred<T>,
    p: TempPred<T>,
    q1: TempPred<T>,
    q2: TempPred<T>,
)
    requires
        spec.entails(always(inv)),
        spec.entails(p.leads_to(always(q1))),
        q1.and(inv).entails(q2),
    ensures
        spec.entails(p.leads_to(always(q2))),
{
    assert forall|ex| #[trigger] spec.satisfied_by(ex) implies p.leads_to(always(q2)).satisfied_by(
        ex,
    ) by {
        assert forall|i| #[trigger] p.satisfied_by(ex.suffix(i)) implies eventually(
            always(q2),
        ).satisfied_by(ex.suffix(i)) by {
            implies_apply(ex, spec, always(inv));
            implies_apply(ex, spec, p.leads_to(always(q1)));
            leads_to_unfold(ex, p, always(q1));
            implies_apply(ex.suffix(i), p, eventually(always(q1)));
            let witness = eventually_choose_witness(ex.suffix(i), always(q1));
            assert forall|j| #[trigger] q2.satisfied_by(ex.suffix(i).suffix(witness).suffix(j)) by {
                assert(ex.suffix(i).suffix(witness).suffix(j) == ex.suffix(i + witness + j));
                implies_apply(ex.suffix(i).suffix(witness).suffix(j), q1.and(inv), q2);
            }
            eventually_proved_by_witness(ex.suffix(i), always(q2), witness);
        }
    }
}

/// Weaken `⇝` by `⇒`.
/// 
/// ## Preconditions  
/// - `spec ⊧ □(p2 ⇒ p1)`  
/// - `spec ⊧ □(q1 ⇒ q2)`  
/// - `spec ⊧ p1 ⇝ q1`
/// ## Postconditions  
/// - `spec ⊧ p2 ⇝ q2`
pub proof fn leads_to_weaken<T>(
    spec: TempPred<T>,
    p1: TempPred<T>,
    q1: TempPred<T>,
    p2: TempPred<T>,
    q2: TempPred<T>,
)
    requires
        spec.entails(always(p2.implies(p1))),
        spec.entails(always(q1.implies(q2))),
        spec.entails(p1.leads_to(q1)),
    ensures
        spec.entails(p2.leads_to(q2)),
{
    always_implies_to_leads_to::<T>(spec, p2, p1);
    always_implies_to_leads_to::<T>(spec, q1, q2);
    leads_to_trans::<T>(spec, p2, p1, q1);
    leads_to_trans::<T>(spec, p2, q1, q2);
}

/// Proving `p ⇝ q` vacuously.
/// 
/// ## Preconditions  
/// - `spec ⊧ □r`  
/// - `p ∧ r == false`
/// ## Postconditions
/// - `spec ⊧ p ⇝ q`
pub proof fn vacuous_leads_to<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        spec.entails(always(r)),
        p.and(r) == false_pred::<T>(),
    ensures
        spec.entails(p.leads_to(q)),
{
    broadcast use {always_unfold, implies_apply, group_execution_suffix_lemmas};

    assert forall|ex| #[trigger] spec.satisfied_by(ex) implies p.leads_to(q).satisfied_by(ex) by {
        assert forall|i| #[trigger] p.satisfied_by(ex.suffix(i)) implies eventually(q).satisfied_by(
            ex.suffix(i),
        ) by {
            assert_by(
                !p.satisfied_by(ex.suffix(i)),
                {
                    implies_apply::<T>(ex, spec, always(r));
                    if p.satisfied_by(ex.suffix(i)) {
                        assert(p.and(r).satisfied_by(ex.suffix(i)));
                    }
                },
            );
        }
    }
}

/// Derive `p ⇝ q` from `□p ⇝ q` with the assumption that `p` is preserved unless `q` happens.
/// 
/// This lemma is useful if we want to show that given `□p ⇝ q`, `q` will eventually hold
/// even if `□p` doesn't hold, as long as `p` is preserved until `q` happens.
/// A concrete usage is to reason about a pair of concurrent components A and B, where
/// (1) A guarantees `□p ⇝ q`, and (2) B makes `p` hold at some point and keeps `p` until `q` holds.
/// Note that we formalize "p is preserved until q happens" using `□(p ∧ next ⇒ p' ∨ q')`:
/// if `p` holds now, then for any possible next state, either `p` or `q` holds.
/// 
/// ## Preconditions  
/// - `spec ⊧ □p ⇝ q`  
/// - `spec ⊧ □(p ∧ next ⇒ p' ∨ q')`  
/// - `spec ⊧ □next`  
/// ## Postconditions  
///  - `spec ⊧ p ⇝ q`
pub proof fn strengthen_leads_to_with_until<T>(
    spec: TempPred<T>,
    next: TempPred<T>,
    p: TempPred<T>,
    q: TempPred<T>,
)
    requires
        spec.entails(always(p).leads_to(q)),
        spec.entails(always(p.and(next).implies(later(p).or(later(q))))),
        spec.entails(always(next)),
    ensures
        spec.entails(p.leads_to(q)),
{
    broadcast use {
        always_unfold,
        implies_apply,
        group_execution_suffix_lemmas,
        group_definition_basics,
    };

    assert forall|ex| #[trigger] spec.satisfied_by(ex) implies p.leads_to(q).satisfied_by(ex) by {
        implies_apply(ex, spec, always(next));
        implies_apply(ex, spec, always(p.and(next).implies(later(p).or(later(q)))));
        always_p_or_eventually_q(ex, next, p, q);
        assert forall|i| #[trigger] p.satisfied_by(ex.suffix(i)) implies eventually(q).satisfied_by(
            ex.suffix(i),
        ) by {
            if always(p).satisfied_by(ex.suffix(i)) {
                implies_apply(ex, spec, always(p).leads_to(q));
            }
        }
    }
}

/// Get a new `⇝` condition with an until condition.
///
/// This lemma can be used in compositional proof.
/// Suppose that a system consists of two concurrent components `A` and `B`,
/// and we want to prove that the entire system makes `P1 ⇝ P3`.
/// If we have already proved that   
/// (1) `A` makes `P1 ⇝ P2` hold, and  
/// (2) `P2` holds until `P3` holds, and  
/// (3) if `P2` holds until `P3` holds, then `B` makes `P2 ⇝ P3`  
/// (in other words, `B` requires that `P2` should hold until `B` makes `P3` hold),
/// then we can apply this lemma and prove that the entire system makes `P2 ⇝ P3`,
/// then by transitivity we have `P1 ⇝ P3`.
/// 
/// Such a case could happen between components with liveness dependencies:
/// `A` at some point needs to delegate the task to `B` and `A` needs to wait until `B` finish
/// so `A` can start the next task, meanwhile when `B` is working `A` should not disable `B`'s
/// progress (i.e., `A` should make sure `P2` holds until `P3` holds).
///
/// ## Preconditions  
/// - `spec ⊧ p1 ⇝ q1`  
/// - `spec ⊧ □(p2 ∧ next ⇒ p2' ∨ q2')`  
/// - `spec ⊧ □next`  
/// ## Postconditions  
/// - `spec ⊧ p1 ∧ p2 ⇝ (q1 ∧ p2) ∨ q2`
pub proof fn transform_leads_to_with_until<T>(
    spec: TempPred<T>,
    next: TempPred<T>,
    p1: TempPred<T>,
    q1: TempPred<T>,
    p2: TempPred<T>,
    q2: TempPred<T>,
)
    requires
        spec.entails(p1.leads_to(q1)),
        spec.entails(always(p2.and(next).implies(later(p2).or(later(q2))))),
        spec.entails(always(next)),
    ensures
        spec.entails(p1.and(p2).leads_to((q1.and(p2)).or(q2))),
{
    broadcast use {
        always_unfold,
        implies_apply,
        group_execution_suffix_lemmas,
        group_definition_basics,
    };

    assert forall|ex| #[trigger] spec.satisfied_by(ex) implies p1.and(p2).leads_to(
        (q1.and(p2)).or(q2),
    ).satisfied_by(ex) by {
        assert forall|i| #[trigger] p1.and(p2).satisfied_by(ex.suffix(i)) implies eventually(
            (q1.and(p2)).or(q2),
        ).satisfied_by(ex.suffix(i)) by {
            implies_apply::<T>(ex, spec, always(next));
            implies_apply::<T>(ex, spec, always(p2.and(next).implies(later(p2).or(later(q2)))));

            always_p_or_eventually_q::<T>(ex, next, p2, q2);

            implies_apply::<T>(ex, spec, p1.leads_to(q1));

            if eventually(q2).satisfied_by(ex.suffix(i)) {
                let witness_idx = eventually_choose_witness::<T>(ex.suffix(i), q2);
                eventually_proved_by_witness::<T>(ex.suffix(i), (q1.and(p2)).or(q2), witness_idx);
            } else {
                let witness_idx = eventually_choose_witness::<T>(ex.suffix(i), q1);
                eventually_proved_by_witness::<T>(ex.suffix(i), (q1.and(p2)).or(q2), witness_idx);
            }
        }
    }
}

/// Concluding `p(n) ⇝ p(0)` using ranking functions, with a step of one.
/// 
/// ## Preconditions  
/// - `forall |n: nat|, n > 0 ==> spec ⊧ p(n) ⇝ p(n - 1)`
/// ## Postconditions  
///  - `forall |n: nat|, spec ⊧ p(n) ⇝ p(0)`
pub proof fn leads_to_rank_step_one<T>(spec: TempPred<T>, p: spec_fn(nat) -> TempPred<T>)
    requires
        forall|n: nat| #![trigger p(n)] (n > 0 ==> spec.entails(p(n).leads_to(p((n - 1) as nat)))),
    ensures
        forall|n: nat| #[trigger] spec.entails(p(n).leads_to(p(0))),
{
    let pre = {
        forall|n: nat| #![trigger p(n)] (n > 0 ==> spec.entails(p(n).leads_to(p((n - 1) as nat))))
    };
    assert forall|n: nat| pre implies #[trigger] spec.entails(p(n).leads_to(p(0))) by {
        leads_to_rank_step_one_help(spec, p, n);
    }
}

proof fn leads_to_rank_step_one_help<T>(spec: TempPred<T>, p: spec_fn(nat) -> TempPred<T>, n: nat)
    requires
        forall|n: nat| #![trigger p(n)] (n > 0 ==> spec.entails(p(n).leads_to(p((n - 1) as nat)))),
    ensures
        spec.entails(p(n).leads_to(p(0))),
    decreases n,
{
    if n > 0 {
        // p(n) ⇝ p(n - 1), p(n - 1) ⇝ p(0)
        // combine with leads-to transitivity
        leads_to_rank_step_one_help(spec, p, (n - 1) as nat);
        leads_to_trans_n!(spec, p(n), p((n - 1) as nat), p(0));
    } else {
        // p(0) ⇝ p(0) trivially
        leads_to_self_temp(p(0));
    }
}

/// `usize` version of the proof rule [leads_to_rank_step_one].
pub proof fn leads_to_rank_step_one_usize<T>(spec: TempPred<T>, p: spec_fn(usize) -> TempPred<T>)
    requires
        forall|n: usize|
            #![trigger p(n)]
            (n > 0 ==> spec.entails(p(n).leads_to(p((n - 1) as usize)))),
    ensures
        forall|n: usize| #[trigger] spec.entails(p(n).leads_to(p(0))),
{
    let pre = {
        forall|n: usize|
            #![trigger p(n)]
            (n > 0 ==> spec.entails(p(n).leads_to(p((n - 1) as usize))))
    };
    assert forall|n: usize| pre implies #[trigger] spec.entails(p(n).leads_to(p(0))) by {
        leads_to_rank_step_one_usize_help(spec, p, n);
    }
}

proof fn leads_to_rank_step_one_usize_help<T>(
    spec: TempPred<T>,
    p: spec_fn(usize) -> TempPred<T>,
    n: usize,
)
    requires
        forall|n: usize|
            #![trigger p(n)]
            (n > 0 ==> spec.entails(p(n).leads_to(p((n - 1) as usize)))),
    ensures
        spec.entails(p(n).leads_to(p(0))),
    decreases n,
{
    if n > 0 {
        // p(n) ⇝ p(n - 1), p(n - 1) ⇝ p(0)
        // combine with leads-to transitivity
        leads_to_rank_step_one_usize_help(spec, p, (n - 1) as usize);
        leads_to_trans_n!(spec, p(n), p((n - 1) as usize), p(0));
    } else {
        // p(0) ⇝ p(0) trivially
        leads_to_self_temp(p(0));
    }
}

// Rules about state machine transitions.
/// Prove safety by induction.
/// 
/// ## Preconditions  
/// - `⊧ init ⇒ inv``
/// - `⊧ inv ∧ next ⇒ inv'`
/// - `spec ⊧ init ∧ □next`
/// ## Postconditions  
/// - `spec ⊧ □inv`
pub proof fn init_invariant<T>(
    spec: TempPred<T>,
    init: StatePred<T>,
    next: ActionPred<T>,
    inv: StatePred<T>,
)
    requires
        forall|s: T| #[trigger] init.apply(s) ==> inv.apply(s),
        forall|s, s_prime: T|
            inv.apply(s) && #[trigger] next.apply(s, s_prime) ==> inv.apply(s_prime),
        spec.entails(lift_state(init)),
        spec.entails(always(lift_action(next))),
    ensures
        spec.entails(always(lift_state(inv))),
{
    broadcast use group_tla_rules;

    assert forall|ex: Execution<T>| spec.satisfied_by(ex) implies #[trigger] always(
        lift_state(inv),
    ).satisfied_by(ex) by {
        implies_apply(ex, spec, lift_state(init));
        implies_apply(ex, spec, always(lift_action(next)));
        assert forall|i: nat| inv.apply(#[trigger] ex.suffix(i).head()) by {
            init_invariant_rec(ex, init, next, inv, i);
        };
    };
}

/// Implies new invariant from proved invariant by induction.
/// 
/// ## Preconditions  
/// - `⊧ init ⇒ inv`  
/// - `⊧ inv ∧ proved_inv ∧ next ⇒ inv'`  
/// - `spec ⊧ init ∧ □next ∧ □proved_inv`  
/// ## Postconditions  
/// - `spec ⊧ □inv`
pub proof fn implies_new_invariant<T>(
    spec: TempPred<T>,
    init: StatePred<T>,
    next: ActionPred<T>,
    inv: StatePred<T>,
    proved_inv: StatePred<T>,
)
    requires
        forall|s: T| #[trigger] init.apply(s) ==> inv.apply(s),
        forall|s, s_prime: T|
            inv.apply(s) && proved_inv.apply(s) && #[trigger] next.apply(s, s_prime) ==> inv.apply(
                s_prime,
            ),
        spec.entails(lift_state(init)),
        spec.entails(always(lift_action(next))),
        spec.entails(always(lift_state(proved_inv))),
    ensures
        spec.entails(always(lift_state(inv))),
{
    broadcast use group_tla_rules;

    assert forall|ex: Execution<T>| spec.satisfied_by(ex) implies #[trigger] always(
        lift_state(inv),
    ).satisfied_by(ex) by {
        implies_apply(ex, spec, lift_state(init));
        implies_apply(ex, spec, always(lift_action(next)));
        implies_apply(ex, spec, always(lift_state(proved_inv)));
        assert forall|i: nat| inv.apply(#[trigger] ex.suffix(i).head()) by {
            implies_new_invariant_rec(ex, init, next, inv, proved_inv, i);
        };
    };
}

/// Get the initial `⇝`.
/// 
/// ## Preconditions  
/// - `spec ⊧ □(p ∧ next ⇒ p' ∨ q')`  
/// - `spec ⊧ □(p ∧ next ∧ forward ⇒ q')`  
/// - `spec ⊧ □next`  
/// - `spec ⊧ □p ⇝ forward`
/// ## Postconditions  
/// - `spec ⊧ p ⇝ q`
pub proof fn wf1_variant_temp<T>(
    spec: TempPred<T>,
    next: TempPred<T>,
    forward: TempPred<T>,
    p: TempPred<T>,
    q: TempPred<T>,
)
    requires
        spec.entails(always(p.and(next).implies(later(p).or(later(q))))),
        spec.entails(always(p.and(next).and(forward).implies(later(q)))),
        spec.entails(always(next)),
        spec.entails(always(p).leads_to(forward)),
    ensures
        spec.entails(p.leads_to(q)),
{
    broadcast use group_tla_rules;

    assert forall|ex| #[trigger] spec.satisfied_by(ex) implies p.leads_to(q).satisfied_by(ex) by {
        assert forall|i| #[trigger] p.satisfied_by(ex.suffix(i)) implies eventually(q).satisfied_by(
            ex.suffix(i),
        ) by {
            implies_apply::<T>(ex, spec, always(next));
            implies_apply::<T>(ex, spec, always(p.and(next).implies(later(p).or(later(q)))));
            implies_apply::<T>(ex, spec, always(p.and(next).and(forward).implies(later(q))));

            always_p_or_eventually_q::<T>(ex, next, p, q);
            implies_apply::<T>(ex.suffix(i), p, always(p).or(eventually(q)));
            if always(p).satisfied_by(ex.suffix(i)) {
                implies_apply::<T>(ex, spec, always(p).leads_to(forward));
                leads_to_unfold::<T>(ex, always(p), forward);
                implies_apply::<T>(ex.suffix(i), always(p), eventually(forward));
                let witness_idx = eventually_choose_witness::<T>(ex.suffix(i), forward);

                always_propagate_forwards::<T>(ex, next, i);
                always_propagate_forwards::<T>(ex, p.and(next).and(forward).implies(later(q)), i);
                implies_apply::<T>(
                    ex.suffix(i).suffix(witness_idx),
                    p.and(next).and(forward),
                    later(q),
                );
                assert(ex.suffix(i).suffix(witness_idx).suffix(1) == ex.suffix(i).suffix(
                    witness_idx + 1,
                ));
                eventually_proved_by_witness::<T>(ex.suffix(i), q, witness_idx + 1);
            }
        }
    }
}

/// Get the initial `⇝` with a stronger wf assumption than [`wf1_variant_temp`].
/// 
/// ## Preconditions  
/// - `⊧ p ∧ next ⇒ p' ∨ q'`  
/// - `⊧ p ∧ next ∧ forward ⇒ q'`  
/// - `⊧ p ⇒ enabled(forward)`  
/// - `spec ⊧ □lift_action(next)`  
/// - `spec ⊧ wf(forward)` 
/// ## Postconditions    
/// - `spec ⊧ p ⇝ q`
pub proof fn wf1<T>(
    spec: TempPred<T>,
    next: ActionPred<T>,
    forward: ActionPred<T>,
    p: StatePred<T>,
    q: StatePred<T>,
)
    requires
        forall|s, s_prime: T|
            p.apply(s) && #[trigger] next.apply(s, s_prime) ==> p.apply(s_prime) || q.apply(
                s_prime,
            ),
        forall|s, s_prime: T|
            p.apply(s) && #[trigger] next.apply(s, s_prime) && forward.apply(s, s_prime)
                ==> q.apply(s_prime),
        forall|s: T| #[trigger] p.apply(s) ==> enabled(forward).apply(s),
        spec.entails(always(lift_action(next))),
        spec.entails(weak_fairness(forward)),
    ensures
        spec.entails(lift_state(p).leads_to(lift_state(q))),
{
    broadcast use group_tla_rules;

    assert forall|ex| #[trigger] spec.satisfied_by(ex) implies always(lift_state(p)).leads_to(
        lift_action(forward),
    ).satisfied_by(ex) by {
        assert forall|i| #[trigger]
            always(lift_state(p)).satisfied_by(ex.suffix(i)) implies eventually(
            lift_action(forward),
        ).satisfied_by(ex.suffix(i)) by {
            implies_apply_with_always::<T>(
                ex.suffix(i),
                lift_state(p),
                lift_state(enabled(forward)),
            );
            assert(ex.suffix(i).suffix(0) == ex.suffix(i));

            implies_apply::<T>(ex, spec, weak_fairness(forward));
            weak_fairness_unfold::<T>(ex, forward);
            implies_apply::<T>(
                ex.suffix(i),
                lift_state(enabled(forward)),
                eventually(lift_action(forward)),
            );
        };
    };
    wf1_variant_temp::<T>(
        spec,
        lift_action(next),
        lift_action(forward),
        lift_state(p),
        lift_state(q),
    );
}

/// Get the initial `⇝` with a stronger wf assumption by borrowing existing inv.
/// 
/// ## Preconditions  
/// - `⊧ p ∧ inv ∧ next ⇒ p' ∨ q'`  
/// - `⊧ p ∧ inv ∧ next ∧ forward ⇒ q'`  
/// - `⊧ p ∧ inv ⇒ enabled(forward)`  
/// - `spec ⊧ □lift_action(next)`  
/// - `spec ⊧ □lift_state(inv)`  
/// - `spec ⊧ wf(forward)`   
/// ## Postconditions  
/// - `spec ⊧ p ⇝ q`
pub proof fn wf1_by_borrowing_inv<T>(
    spec: TempPred<T>,
    next: ActionPred<T>,
    forward: ActionPred<T>,
    p: StatePred<T>,
    q: StatePred<T>,
    inv: StatePred<T>,
)
    requires
        forall|s, s_prime: T|
            p.apply(s) && inv.apply(s) && #[trigger] next.apply(s, s_prime) ==> p.apply(s_prime)
                || q.apply(s_prime),
        forall|s, s_prime: T|
            p.apply(s) && inv.apply(s) && #[trigger] next.apply(s, s_prime) && forward.apply(
                s,
                s_prime,
            ) ==> q.apply(s_prime),
        forall|s: T| #[trigger] p.apply(s) && inv.apply(s) ==> enabled(forward).apply(s),
        spec.entails(always(lift_action(next))),
        spec.entails(always(lift_state(inv))),
        spec.entails(weak_fairness(forward)),
    ensures
        spec.entails(lift_state(p).leads_to(lift_state(q))),
{
    broadcast use group_tla_rules;

    let next_and_inv = lift_action(next).and(lift_state(inv));

    assert forall|ex| #[trigger] spec.satisfied_by(ex) implies always(
        lift_state(p).and(lift_state(inv)),
    ).leads_to(lift_action(forward)).satisfied_by(ex) by {
        assert forall|i| #[trigger]
            always(lift_state(p).and(lift_state(inv))).satisfied_by(
                ex.suffix(i),
            ) implies eventually(lift_action(forward)).satisfied_by(ex.suffix(i)) by {
            implies_apply_with_always::<T>(
                ex.suffix(i),
                lift_state(p).and(lift_state(inv)),
                lift_state(enabled(forward)),
            );
            assert(ex.suffix(i).suffix(0) == ex.suffix(i));
            implies_apply::<T>(ex, spec, weak_fairness(forward));
            weak_fairness_unfold::<T>(ex, forward);
            implies_apply::<T>(
                ex.suffix(i),
                lift_state(enabled(forward)),
                eventually(lift_action(forward)),
            );
        };
    };
    entails_always_and_n!(spec, lift_action(next), lift_state(inv));
    always_and_equality(lift_state(p), lift_state(inv));
    always_double_equality(lift_state(inv));
    leads_to_by_borrowing_inv(
        spec,
        always(lift_state(p)),
        lift_action(forward),
        always(lift_state(inv)),
    );
    wf1_variant_temp::<T>(spec, next_and_inv, lift_action(forward), lift_state(p), lift_state(q));
}

/// Strengthen next with inv.
/// 
/// ## Preconditions  
/// - `spec ⊧ □next`  
/// - `spec ⊧ □inv`  
/// - `⊧ next ∧ inv <=> next_and_inv`  
/// ## Postconditions  
/// - `spec ⊧ □next_and_inv`
pub proof fn strengthen_next<T>(
    spec: TempPred<T>,
    next: ActionPred<T>,
    inv: StatePred<T>,
    next_and_inv: ActionPred<T>,
)
    requires
        spec.entails(always(lift_action(next))),
        spec.entails(always(lift_state(inv))),
        lift_action(next_and_inv).entails(lift_action(next).and(lift_state(inv))),
        lift_action(next).and(lift_state(inv)).entails(lift_action(next_and_inv)),
    ensures
        spec.entails(always(lift_action(next_and_inv))),
{
    entails_and_temp::<T>(spec, always(lift_action(next)), always(lift_state(inv)));
    always_and_equality::<T>(lift_action(next), lift_state(inv));
    temp_pred_equality::<T>(lift_action(next_and_inv), lift_action(next).and(lift_state(inv)));
}

// Macros for multiple-predicate variants of the above rules.
#[macro_export]
macro_rules! leads_to_trans_n {
    [$($tail:tt)*] => {
        ::vstd::prelude::verus_proof_macro_exprs!($crate::temporal_logic::rules::leads_to_trans_n_internal!($($tail)*));
    };
}

#[macro_export]
macro_rules! leads_to_trans_n_internal {
    ($spec:expr, $p1:expr, $p2:expr, $p3:expr $(,)?) => {
        leads_to_trans($spec, $p1, $p2, $p3);
    };
    ($spec:expr, $p1:expr, $p2:expr, $p3:expr, $($tail:tt)*) => {
        leads_to_trans($spec, $p1, $p2, $p3);
        leads_to_trans_n_internal!($spec, $p1, $p3, $($tail)*);
    };
}

pub use leads_to_trans_n;
pub use leads_to_trans_n_internal;

// Combine multiple StatePred using `.and`.
// Usage: state_pred_and!(p1) | p1
//        state_pred_and!(p1, p2) | p1.and(p2)
//        state_pred_and!(p1, p2, p3, ...) | p1.and(p2).and(p3)...
#[macro_export]
macro_rules! state_pred_and {
    ($p1:expr $(,)?) => {
        $p1
    };
    ($p1:expr, $p2:expr $(,)?) => {
        $p1.and($p2)
    };
    ($p1:expr, $p2:expr, $($tail:expr),+ $(,)?) => {
        {
            let tmp = $p1.and($p2);
            $( let tmp = tmp.and($tail); )*
            tmp
        }
    };
}

pub use state_pred_and;

// Combine multiple TempPred using `.and`.
// Usage: temp_pred_and!(p1) | p1
//        temp_pred_and!(p1, p2) | p1.and(p2)
//        temp_pred_and!(p1, p2, p3, ...) | p1.and(p2).and(p3)...
#[macro_export]
macro_rules! temp_pred_and {
    [$($tail:tt)*] => {
        ::verus_builtin_macros::verus_proof_macro_exprs!($crate::temporal_logic::rules::temp_pred_and_internal!($($tail)*))
    }
}

#[macro_export]
macro_rules! temp_pred_and_internal {
    ($next:expr) => {
        $next
    };
    ($next:expr, $($expr:expr),* $(,)?) => {
        $next $(
            .and($expr)
        )*
    };
}

pub use temp_pred_and;
pub use temp_pred_and_internal;

// Entails the conjunction of all the p if entails each of them.
// ## Preconditions
//     spec ⊧ p1
//     spec ⊧ p2
//        ...
//     spec ⊧ pn
// ## Postconditions
//     spec ⊧ p1 ∧ p2 ∧ ... ∧ pn
//
// Usage: entails_and_n!(spec, p1, p2, p3, p4)
#[macro_export]
macro_rules! entails_and_n {
    [$($tail:tt)*] => {
        ::verus_builtin_macros::verus_proof_macro_exprs!($crate::temporal_logic::rules::entails_and_n_internal!($($tail)*));
    };
}

#[macro_export]
macro_rules! entails_and_n_internal {
    ($spec:expr, $p1:expr, $p2:expr $(,)?) => {
        entails_and_temp($spec, $p1, $p2);
    };
    ($spec:expr, $p1:expr, $p2:expr, $($tail:tt)*) => {
        entails_and_temp($spec, $p1, $p2);
        entails_and_n_internal!($spec, $p1.and($p2), $($tail)*);
    };
}

pub use entails_and_n;
pub use entails_and_n_internal;

// Entails □ the conjunction of all the p if entails each always p.
// ## Preconditions
//     spec ⊧ □p1
//     spec ⊧ □p2
//        ...
//     spec ⊧ □pn
// ## Postconditions
//     spec ⊧ □(p1 ∧ p2 ∧ ... ∧ pn)
//
// Usage: entails_always_and_n!(spec, p1, p2, p3, p4)
#[macro_export]
macro_rules! entails_always_and_n {
    [$($tail:tt)*] => {
        ::vstd::prelude::verus_proof_macro_exprs!($crate::temporal_logic::rules::entails_always_and_n_internal!($($tail)*));
    };
}

#[macro_export]
macro_rules! entails_always_and_n_internal {
    ($spec:expr, $p1:expr $(,)?) => {};
    ($spec:expr, $p1:expr, $p2:expr $(,)?) => {
        entails_and_temp($spec, always($p1), always($p2));
        always_and_equality($p1, $p2);
    };
    ($spec:expr, $p1:expr, $p2:expr, $($tail:tt)*) => {
        entails_and_temp($spec, always($p1), always($p2));
        always_and_equality($p1, $p2);
        entails_always_and_n_internal!($spec, $p1.and($p2), $($tail)*);
    };
}

pub use entails_always_and_n;
pub use entails_always_and_n_internal;

#[macro_export]
macro_rules! always_and_equality_n {
    [$($tail:tt)*] => {
        ::verus_builtin_macros::verus_proof_macro_exprs!($crate::temporal_logic::rules::always_and_equality_n_internal!($($tail)*));
    };
}

#[macro_export]
macro_rules! always_and_equality_n_internal {
    ($p1:expr, $p2:expr $(,)?) => {
        always_and_equality($p1, $p2);
    };
    ($p1:expr, $p2:expr, $($tail:tt)*) => {
        always_and_equality($p1, $p2);
        always_and_equality_n_internal!($p1.and($p2), $($tail)*);
    };
}

pub use always_and_equality_n;
pub use always_and_equality_n_internal;

// □(lift_state(state_pred_and!(p1, p2, ..., pn))) == □(lift_state(p1)).and(□(lift_state(p2))).and(...).and(□(lift_state(pn)))
#[macro_export]
macro_rules! always_lift_state_and_equality_n {
    [$($tail:tt)*] => {
        ::verus_builtin_macros::verus_proof_macro_exprs!($crate::temporal_logic::rules::always_lift_state_and_equality_n_internal!($($tail)*));
    };
}

#[macro_export]
macro_rules! always_lift_state_and_equality_n_internal {
    ($p1:expr, $p2:expr $(,)?) => {
        always_lift_state_and_equality($p1, $p2);
    };
    ($p1:expr, $p2:expr, $($tail:tt)*) => {
        always_lift_state_and_equality($p1, $p2);
        always_lift_state_and_equality_n_internal!(state_pred_and!($p1, $p2), $($tail)*);
    };
}

pub use always_lift_state_and_equality_n;
pub use always_lift_state_and_equality_n_internal;

// Combine the premises of all the leads_to using or.
// ## Preconditions
//     spec ⊧ p1 ⇝ q
//     spec ⊧ p2 ⇝ q
//         ...
//     spec ⊧ pn ⇝ q
// ## Postconditions
//     spec ⊧ (p1 ∨ p2 ∨ ... ∨ pn) ⇝ q
//
// Usage: or_leads_to_combine_n!(spec, p1, p2, p3, p4; q)
#[macro_export]
macro_rules! or_leads_to_combine_n {
    [$($tail:tt)*] => {
        ::verus_builtin_macros::verus_proof_macro_exprs!($crate::temporal_logic::rules::or_leads_to_combine_n_internal!($($tail)*));
    };
}

#[macro_export]
macro_rules! or_leads_to_combine_n_internal {
    ($spec:expr, $p1:expr, $p2:expr; $q:expr) => {
        or_leads_to_combine($spec, $p1, $p2, $q);
    };
    ($spec:expr, $p1:expr, $p2:expr, $($rest:expr),+; $q:expr) => {
        or_leads_to_combine($spec, $p1, $p2, $q);
        or_leads_to_combine_n_internal!($spec, $p1.or($p2), $($rest),+; $q);
    };
}

pub use or_leads_to_combine_n;
pub use or_leads_to_combine_n_internal;

// Combine or_leads_to_combine and temp_pred_equality.
// The 'result' is the equivalent temporal predicate of joining all following predicates with ∨.
#[macro_export]
macro_rules! or_leads_to_combine_and_equality2 {
    ($spec:expr, $result:expr, $p1:expr, $($rest:expr),+; $q:expr) => {
        temp_pred_equality(
            $result,
            $p1$(.or($rest))+
        );
        or_leads_to_combine_n!($spec, $p1, $($rest),+; $q);
    }
}

pub use or_leads_to_combine_and_equality2;

// Leads to the conjunction of all the □q if leads to each of them.
// ## Preconditions
//     spec ⊧ p ⇝ □q1
//     spec ⊧ p ⇝ □q2
//        ...
//     spec ⊧ p ⇝ □qn
// ## Postconditions
//     spec ⊧ p ⇝ □(q1 ∧ q2 ∧ ... ∧ qn)
//
// Usage: leads_to_always_combine_n!(spec, p, q1, q2, q3, q4)
#[macro_export]
macro_rules! leads_to_always_combine_n {
    [$($tail:tt)*] => {
        ::verus_builtin_macros::verus_proof_macro_exprs!($crate::temporal_logic::rules::leads_to_always_combine_n_internal!($($tail)*));
    };
}

#[macro_export]
macro_rules! leads_to_always_combine_n_internal {
    ($spec:expr, $p:expr, $q1:expr, $q2:expr $(,)?) => {
        leads_to_always_combine($spec, $p, $q1, $q2);
    };
    ($spec:expr, $p:expr, $q1:expr, $q2:expr, $($tail:tt)*) => {
        leads_to_always_combine($spec, $p, $q1, $q2);
        always_and_equality($q1, $q2);
        leads_to_always_combine_n_internal!($spec, $p, $q1.and($q2), $($tail)*);
    };
}

pub use leads_to_always_combine_n;
pub use leads_to_always_combine_n_internal;

#[macro_export]
macro_rules! leads_to_always_combine_n_with_equality {
    [$($tail:tt)*] => {
        ::verus_builtin_macros::verus_proof_macro_exprs!($crate::temporal_logic::rules::leads_to_always_combine_n_with_equality_internal!($($tail)*));
    };
}

#[macro_export]
macro_rules! leads_to_always_combine_n_with_equality_internal {
    ($spec:expr, $p:expr, $dst:expr, $($tail:tt)*) => {
        temp_pred_equality($dst, combine_with_next!($($tail)*));
        leads_to_always_combine_n!($spec, $p, $($tail)*);
    };
}

pub use leads_to_always_combine_n_with_equality;
pub use leads_to_always_combine_n_with_equality_internal;

// Strengthen next with arbitrary number of predicates.
// ## Preconditions
//     spec ⊧ □p1
//     spec ⊧ □p2
//        ...
//     spec ⊧ □pn
//     p1 ∧ p2 ∧ ... ∧ pn ==> partial_spec
// ## Postconditions
//     spec ⊧ □all
//
// Usage: combine_spec_entails_always_n!(spec, partial_spec, p1, p2, p3, p4)
#[macro_export]
macro_rules! combine_spec_entails_always_n {
    [$($tail:tt)*] => {
        ::verus_builtin_macros::verus_proof_macro_exprs!($crate::temporal_logic::rules::combine_spec_entails_always_n_internal!($($tail)*))
    }
}

#[macro_export]
macro_rules! combine_spec_entails_always_n_internal {
    ($spec:expr, $partial_spec:expr, $($tail:tt)*) => {
        assert_by(
            valid($spec.implies(always(temp_pred_and!($($tail)*)))),
            {
                entails_always_and_n!($spec, $($tail)*);
            }
        );
        entails_preserved_by_always(temp_pred_and!($($tail)*), $partial_spec);
        entails_trans($spec, always(temp_pred_and!($($tail)*)), always($partial_spec));
    };
}

pub use combine_spec_entails_always_n;
pub use combine_spec_entails_always_n_internal;

// Combine multiple □ lift_state predicates using AND.
// ## Preconditions
//     spec ⊧ □lift_state(p1)
//     spec ⊧ □lift_state(p2)
//     ...
//     spec ⊧ □lift_state(pn)
// ## Postconditions
// spec ⊧ □lift_state(combine_state_pred!(p1, p2, ..., pn))  // spec ⊧ □lift_state(|s| p1(s) && p2(s) && ... && pn(s))
//
// Usage: entails_always_lift_state_and_n!(spec, p1, p2, p3, p4)
#[macro_export]
macro_rules! entails_always_lift_state_and_n {
    [$($tail:tt)*] => {
        ::vstd::prelude::verus_proof_macro_exprs!($crate::temporal_logic::rules::entails_always_lift_state_and_n_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! entails_always_lift_state_and_n_internal {
    ($spec:expr, $p1:expr) => {
        // Single predicate case: nothing to do
    };
    ($spec:expr, $p1:expr, $p2:expr $(,)?) => {
        // Two predicate case: use entails_always_lift_state_and
        entails_always_lift_state_and($spec, $p1, $p2);
    };
    ($spec:expr, $p1:expr, $p2:expr, $p3:expr $(,)?) => {
        // Three predicate case: build step by step
        entails_always_lift_state_and($spec, $p1, $p2);
        let combined_p1_p2 = state_pred_and!($p1, $p2);
        entails_always_lift_state_and($spec, combined_p1_p2, $p3);
    };
    ($spec:expr, $p1:expr, $p2:expr, $($tail:expr),+ $(,)?) => {
        // Multi predicate case: recursively combine predicates
        entails_always_lift_state_and($spec, $p1, $p2);
        let combined_p1_p2 = state_pred_and!($p1, $p2);
        entails_always_lift_state_and_n_internal!($spec, combined_p1_p2, $($tail),+);
    };
}

pub use entails_always_lift_state_and_n;
pub use entails_always_lift_state_and_n_internal;

// Show that an spec entails the invariant by a group of action/state predicates which are also invariants entailed by spec.
// ## Preconditions
//     partial_spec ⊧ inv
//     spec ⊧ □p1
//     spec ⊧ □p2
//         ...
//     spec ⊧ □pn
//     p1 ∧ p2 ∧ ... ∧ pn ==> partial_spec
// ## Postconditions
//     spec ⊧ □inv
//
// Usage: invariant_n!(spec, partial_spec, inv, p1, p2, ..., pn)
#[macro_export]
macro_rules! invariant_n {
    [$($tail:tt)*] => {
        ::verus_builtin_macros::verus_proof_macro_exprs!($crate::temporal_logic::rules::invariant_n_internal!($($tail)*))
    }
}

#[macro_export]
macro_rules! invariant_n_internal {
    ($spec:expr, $partial_spec:expr, $inv:expr, $($tail:tt)*) => {
        assert_by(
            valid($spec.implies(always(temp_pred_and!($($tail)*)))),
            {
                entails_always_and_n!($spec, $($tail)*);
            }
        );
        entails_preserved_by_always(temp_pred_and!($($tail)*), $partial_spec);
        entails_trans($spec, always(temp_pred_and!($($tail)*)), always($partial_spec));
        entails_preserved_by_always($partial_spec, $inv);
        entails_trans($spec, always($partial_spec), always($inv));
    };
}

pub use invariant_n;
pub use invariant_n_internal;

// The conjunction of all the p is stable if each p is stable.
// ## Preconditions
//     ⊧ stable(p1)
//     ⊧ stable(p2)
//      ...
//     ⊧ stable(pn)
// ## Postconditions
//     ⊧ stable(p1 ∧ p2 ∧ ... ∧ pn)
//
// Usage: stable_and_n!(p1, p2, p3, p4)
#[macro_export]
macro_rules! stable_and_n {
    [$($tail:tt)*] => {
        ::verus_builtin_macros::verus_proof_macro_exprs!($crate::temporal_logic::rules::stable_and_n_internal!($($tail)*));
    };
}

#[macro_export]
macro_rules! stable_and_n_internal {
    ($p1:expr, $p2:expr $(,)?) => {
        stable_and_temp($p1, $p2);
    };
    ($p1:expr, $p2:expr, $($tail:tt)*) => {
        stable_and_temp($p1, $p2);
        stable_and_n_internal!($p1.and($p2), $($tail)*);
    };
}

pub use stable_and_n;
pub use stable_and_n_internal;

// The conjunction of all the p is stable if each p is stable.
// ## Postconditions
//     ⊧ stable(□p1 ∧ □p2 ∧ ... ∧ □pn)
//
// Usage: stable_and_always_n!(p1, p2, p3, p4)
#[macro_export]
macro_rules! stable_and_always_n {
    [$($tail:tt)*] => {
        ::verus_builtin_macros::verus_proof_macro_exprs!($crate::temporal_logic::rules::stable_and_always_n_internal!($($tail)*));
    };
}

#[macro_export]
macro_rules! stable_and_always_n_internal {
    ($p1:expr, $($tail:expr),* $(,)?) => {
        always_p_is_stable($p1);
        $(always_p_is_stable($tail);)*
        stable_and_n!(always($p1), $(always($tail)),*);
    };
}

pub use stable_and_always_n;
pub use stable_and_always_n_internal;

// Implies new invariant from multiple proved invariants.
// ## Preconditions
//     ⊧ init ⇒ inv
//     ⊧ inv ∧ p1 ∧ p2 ∧ ... ∧ pn ∧ next ⇒ inv'
//     spec ⊧ lift_state(init)
//     spec ⊧ □(lift_action(next))
//     spec ⊧ □lift_state(p1)
//     spec ⊧ □lift_state(p2)
//     ...
//     spec ⊧ □lift_state(pn)
// ## Postconditions
//     spec ⊧ □lift_state(inv)
//
// Usage: implies_new_invariant_n!(spec, init, next, inv, p1, p2, p3, ...)
#[macro_export]
macro_rules! implies_new_invariant_n {
    [$($tail:tt)*] => {
        ::vstd::prelude::verus_proof_macro_exprs!($crate::temporal_logic::rules::implies_new_invariant_n_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! implies_new_invariant_n_internal {
    ($spec:expr, $init:expr, $next:expr, $inv:expr, $p1:expr) => {
        implies_new_invariant($spec, $init, $next, $inv, $p1);
    };
    ($spec:expr, $init:expr, $next:expr, $inv:expr, $p1:expr,) => {
        implies_new_invariant_n_internal!($spec, $init, $next, $inv, $p1);
    };
    ($spec:expr, $init:expr, $next:expr, $inv:expr, $($preds:expr),+) => {
        {
            let combined_pred = state_pred_and!($($preds),+);
            entails_always_lift_state_and_n!($spec, $($preds),+);
            implies_new_invariant($spec, $init, $next, $inv, combined_pred);
        }
    };
    ($spec:expr, $init:expr, $next:expr, $inv:expr, $($preds:expr),+ ,) => {
        implies_new_invariant_n_internal!($spec, $init, $next, $inv, $($preds),+);
    };
}

pub use implies_new_invariant_n;
pub use implies_new_invariant_n_internal;

// Strengthen wf1_by_borrowing_inv with multiple invariants.
// ## Preconditions
//     spec ⊧ □next
//     spec ⊧ □inv1
//     spec ⊧ □inv2
//        ...
//     spec ⊧ □invn
//     ⊧ p ∧ inv1 ∧ inv2 ∧ ... ∧ invn ∧ next ⇒ p' ∨ q'
//     ⊧ p ∧ inv1 ∧ inv2 ∧ ... ∧ invn ∧ next ∧ forward ⇒ q'
//     ⊧ p ∧ inv1 ∧ inv2 ∧ ... ∧ invn ⇒ enabled(forward)
//     spec ⊧ wf(forward)
// ## Postconditions
//     spec ⊧ p ⇝ q
// Usage: wf1_by_borrowing_inv_n!(spec, next, forward, p, q, inv1, inv2, inv3, ...)
#[macro_export]
macro_rules! wf1_by_borrowing_inv_n {
    ($spec:expr, $next:expr, $forward:expr, $p:expr, $q:expr, $($inv:expr),+ $(,)?) => {{
        entails_always_lift_state_and_n!($spec, $($inv),+);
        // Explicitly call the base case to ensure we have the needed condition
        let combined_inv = state_pred_and!($($inv),+);
        // After entails_always_lift_state_and_n!, we should have spec.entails(always(lift_state(combined_inv)))
        wf1_by_borrowing_inv($spec, $next, $forward, $p, $q, combined_inv)
    }};
}

pub use wf1_by_borrowing_inv_n;

// Apply always_lift_state_weaken with multiple predicates.
// ## Preconditions
//     forall |s| p1(s) && p2(s) && ... && pn(s) ==> h(s)
//     spec ⊧ □lift_state(p1)
//     spec ⊧ □lift_state(p2)
//     ...
//     spec ⊧ □lift_state(pn)
// ## Postconditions
//     spec ⊧ □lift_state(h)
//
// Usage: always_lift_state_weaken_n!(spec, p1, p2, p3, ..., h)
#[macro_export]
macro_rules! always_lift_state_weaken_n {
    [$($tail:tt)*] => {
        ::vstd::prelude::verus_proof_macro_exprs!($crate::temporal_logic::rules::always_lift_state_weaken_n_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! always_lift_state_weaken_n_internal {
    ($spec:expr, $p1:expr, $h:expr) => {
        always_lift_state_weaken($spec, $p1, $h);
    };
    ($spec:expr, $p1:expr, $p2:expr, $h:expr) => {
        entails_always_lift_state_and_n!($spec, $p1, $p2);
        always_lift_state_weaken($spec, state_pred_and!($p1, $p2), $h);
    };
    ($spec:expr, $p1:expr, $p2:expr, $h:expr,) => {
        always_lift_state_weaken_n_internal!($spec, $p1, $p2, $h);
    };
    ($spec:expr, $p1:expr, $p2:expr, $($tail:expr),+ , $h:expr) => {
        entails_always_lift_state_and_n!($spec, $p1, $p2, $($tail),+);
        always_lift_state_weaken($spec, state_pred_and!($p1, $p2, $($tail),+), $h);
    };
    ($spec:expr, $p1:expr, $p2:expr, $($tail:expr),+ , $h:expr,) => {
        always_lift_state_weaken_n_internal!($spec, $p1, $p2, $($tail),+ , $h);
    };
}

pub use always_lift_state_weaken_n;
pub use always_lift_state_weaken_n_internal;

pub broadcast group group_tla_rules {
    state_pred_and_apply_equality,
    state_pred_or_apply_equality,
    state_pred_implies_apply_equality,
    state_pred_not_apply_equality,
    lift_state_and_equality,
    lift_state_or_equality,
    lift_state_not_equality,
    lift_state_implies_equality,
    entails_and_temp,
    entails_and_temp_reverse,
    entails_or_temp,
    entails_not_temp_reverse,
    entails_implies_temp_reverse,
    always_lift_state_and_equality,
    always_implies_to_leads_to,
    always_to_always_later,
    always_double_equality,
    always_and_equality,
    tla_forall_apply,
    spec_entails_tla_forall,  // may slow down proofs
    always_implies_forall_intro,  // may slow down proofs
    tla_exists_leads_to_intro,  // may slow down proofs
    leads_to_self_temp,
    entails_and_different_temp,
    always_p_is_stable,
    stable_and_temp,
    entails_preserved_by_always,
    leads_to_apply,  // may slow down proofs
    or_leads_to_combine,
    leads_to_always_combine,
    leads_to_framed_by_or,
    lift_state_exists_equality,
    implies_tla_exists_intro,
    leads_to_tla_exists_intro,
    state_exists_intro,  // may be unnecessary
    entails_always_lift_state_and,  // may slow down proofs
    entails_always_lift_state_and_elim,
    entails_tla_exists_by_witness,  // may slow down proofs
    lift_state_exists_leads_to_intro,
    lift_state_exists_absorb_equality,
    lift_state_forall_absorb_equality,
    lift_state_not_equality,
}

} // verus!
