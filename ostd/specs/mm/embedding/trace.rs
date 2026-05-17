//! Lazy trace generation: [`run`] generates a trace on the fly by
//! repeatedly stepping with arbitrary-but-valid Ops.
//!
//! At each iteration `run` uses `choose` to pick *some* `Op` that
//! satisfies [`super::op_pre`] against the current store. Because
//! [`super::Op::NewVmSpace`] has no precondition, such an op always
//! exists, so `choose` is well-defined. The picked op is then
//! discharged into [`super::step`], and the recursion continues with
//! the post-state.
//!
//! Compared to the previous `run_trace(trace: Seq<Op>)` design, this
//! avoids needing a `valid_trace` predicate / `step_post` spec
//! function: validity is established at the moment of choice rather
//! than as a precondition over a pre-built trace.

use vstd::prelude::*;
use vstd_extra::ownership::*;

use super::{op_pre, step, Op, VmStore};

verus! {

/// `op_pre` is always satisfiable: [`Op::NewVmSpace`] has no
/// preconditions, so it's a witness for any state.
pub proof fn op_pre_satisfiable<'rcu>(s: VmStore<'rcu>)
    ensures
        exists|op: Op| op_pre(s, op),
{
    assert(op_pre(s, Op::NewVmSpace));
}

/// Generates a trace of `n` steps by repeatedly choosing some op that
/// satisfies [`super::op_pre`] against the current store and applying
/// it via [`super::step`]. Preserves [`VmStore::inv`] throughout.
///
/// This is the soundness story over arbitrary call sequences: no
/// matter which `n` operations the system picks (subject only to
/// op-pre validity at each step), invariants hold.
pub proof fn run<'rcu>(tracked s: &mut VmStore<'rcu>, n: nat)
    requires
        old(s).inv(),
    ensures
        final(s).inv(),
    decreases n,
{
    if n > 0 {
        op_pre_satisfiable(*s);
        let op: Op = choose|op: Op| op_pre(*s, op);
        step(s, op);
        run(s, (n - 1) as nat);
    }
}

} // verus!
