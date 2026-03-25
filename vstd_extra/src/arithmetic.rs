use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::{pervasive::trigger, prelude::*};

verus! {

pub open spec fn nat_align_down(x: nat, align: nat) -> nat
    recommends
        align > 0,
{
    (x - x % align) as nat
}

pub open spec fn nat_align_up(x: nat, align: nat) -> nat
    recommends
        align > 0,
{
    if x % align == 0 {
        x
    } else {
        nat_align_down(x, align) + align
    }
}

pub broadcast proof fn lemma_nat_align_up_sound(x: nat, align: nat)
    requires
        align > 0,
    ensures
        #[trigger] nat_align_up(x, align) >= x,
        nat_align_up(x, align) % align == 0,
        forall|n: nat| n >= x && #[trigger] (n % align) == 0 ==> n >= nat_align_up(x, align),
        nat_align_up(x, align) - x < align,
{
    if x % align == 0 {
    } else {
        let down = nat_align_down(x, align);
        lemma_fundamental_div_mod(x as int, align as int);
        lemma_mul_is_commutative(align as int, x as int / align as int);
        lemma_mod_multiples_basic(x as int / align as int, align as int);
        lemma_mod_add_multiples_vanish(down as int, align as int);
    }

    assert forall|n: nat| n >= x && (#[trigger] (n % align)) == 0 implies n >= nat_align_up(
        x,
        align,
    ) by {
        if x % align == 0 {
        } else {
            lemma_mul_is_commutative(align as int, x as int / align as int);

            lemma_fundamental_div_mod(n as int, align as int);
            if n < nat_align_up(x, align) {
                let q_n = n as int / align as int;
                let q_x = x as int / align as int;
                lemma_mul_is_distributive_add(align as int, q_x, 1);
                if q_n >= q_x + 1 {
                    lemma_mul_inequality(q_x + 1, q_n, align as int);
                    lemma_mul_is_commutative(align as int, q_n);
                }
                lemma_mul_inequality(q_n, q_x, align as int);
                lemma_mul_is_commutative(align as int, q_n);
            }
        }
    }
}

pub broadcast proof fn lemma_nat_align_down_sound(x: nat, align: nat)
    requires
        align > 0,
    ensures
        #[trigger] nat_align_down(x, align) <= x,
        nat_align_down(x, align) % align == 0,
        forall|n: nat| n <= x && #[trigger] (n % align) == 0 ==> n <= nat_align_down(x, align),
        x - nat_align_down(x, align) < align,
{
    lemma_fundamental_div_mod(x as int, align as int);
    let q_x = x as int / align as int;
    lemma_mod_multiples_basic(q_x, align as int);
    lemma_mul_is_commutative(align as int, q_x);

    assert forall|n: nat| n <= x && #[trigger] (n % align) == 0 implies n <= nat_align_down(
        x,
        align,
    ) by {
        if n > nat_align_down(x, align) && n % align == 0 {
            lemma_fundamental_div_mod(n as int, align as int);
            let q_n = n as int / align as int;
            if q_n <= q_x {
                lemma_mul_inequality(q_n, q_x, align as int);
                lemma_mul_is_commutative(align as int, q_n);
            } else {
                lemma_mul_inequality(q_x + 1, q_n, align as int);
                lemma_mul_is_commutative(align as int, q_n);
                lemma_mul_is_distributive_add(align as int, q_x, 1);
            }
        }
    }
}

/// When `k2` is a multiple of `k1`, aligning to the coarser `k2` gives a
/// value at most `nat_align_down(x, k1)`: the `k2`-boundary is also a
/// `k1`-boundary, and it is the largest such boundary ≤ x.
pub proof fn lemma_nat_align_down_monotone(x: nat, k1: nat, k2: nat)
    requires
        k1 > 0,
        k2 > 0,
        k2 % k1 == 0,
    ensures
        nat_align_down(x, k2) <= nat_align_down(x, k1),
        nat_align_down(x, k2) % k1 == 0,
{
    lemma_nat_align_down_sound(x, k1);
    lemma_nat_align_down_sound(x, k2);
    // Prove nat_align_down(x, k2) is k1-aligned:
    // nat_align_down(x, k2) = q * k2 where k2 = r * k1, so = q * r * k1.
    let a = nat_align_down(x, k2) as int;
    let q = a / k2 as int;
    let r = k2 as int / k1 as int;
    lemma_fundamental_div_mod(a, k2 as int);
    assert(a == q * k2 as int);
    lemma_fundamental_div_mod(k2 as int, k1 as int);
    assert(k2 as int == r * k1 as int);
    // a == q * (r * k1)
    assert(a == q * (r * k1 as int));
    // q * (r * k1) == (q * r) * k1
    lemma_mul_is_associative(q, r, k1 as int);
    assert(a == (q * r) * k1 as int);
    // (q * r) * k1 % k1 == 0
    lemma_mod_multiples_basic(q * r, k1 as int);
    assert(nat_align_down(x, k2) % k1 == 0);
}

/// The finer-aligned block `[align_down(x,k1), align_down(x,k1)+k1)` fits
/// inside the coarser-aligned block `[align_down(x,k2), align_down(x,k2)+k2)`
/// when `k1` divides `k2`.
pub proof fn lemma_nat_align_down_within_block(x: nat, k1: nat, k2: nat)
    requires
        k1 > 0,
        k2 > 0,
        k2 % k1 == 0,
    ensures
        nat_align_down(x, k1) + k1 <= nat_align_down(x, k2) + k2,
{
    lemma_nat_align_down_sound(x, k1);
    lemma_nat_align_down_sound(x, k2);
    lemma_nat_align_down_monotone(x, k1, k2);
    // nat_align_down(x, k2) <= nat_align_down(x, k1) <= x < nat_align_down(x, k2) + k2
    // So nat_align_down(x, k1) < nat_align_down(x, k2) + k2.
    // Both are k1-aligned, so the gap nat_align_down(x,k1) - nat_align_down(x,k2)
    // is a multiple of k1 that is strictly less than k2, hence <= k2 - k1.
    // Therefore nat_align_down(x,k1) + k1 <= nat_align_down(x,k2) + k2.
    // Both values are k1-aligned; their difference is a multiple of k1.
    let a1 = nat_align_down(x, k1) as int;
    let a2 = nat_align_down(x, k2) as int;
    let diff = a1 - a2;
    assert(diff >= 0);
    assert(diff < k2 as int);
    // a1 = q1 * k1, a2 = q2 * k1 (both k1-aligned)
    let q1 = a1 / k1 as int;
    let q2 = a2 / k1 as int;
    lemma_fundamental_div_mod(a1, k1 as int);
    lemma_fundamental_div_mod(a2, k1 as int);
    // a2 is also k1-aligned (from monotone proof)
    lemma_nat_align_down_monotone(x, k1, k2);
    // a1 == q1 * k1, a2 == q2 * k1, so diff == (q1 - q2) * k1
    assert(a1 == q1 * k1 as int);
    assert(a2 == q2 * k1 as int);
    lemma_mul_is_distributive_sub(k1 as int, q1, q2);
    lemma_mul_is_commutative(k1 as int, q1);
    lemma_mul_is_commutative(k1 as int, q2);
    lemma_mul_is_commutative(k1 as int, q1 - q2);
    assert(diff == (q1 - q2) * k1 as int);
    // k2 == qk * k1
    let qk = k2 as int / k1 as int;
    lemma_fundamental_div_mod(k2 as int, k1 as int);
    assert(k2 as int == qk * k1 as int);
    lemma_mul_is_commutative(k1 as int, qk);
    // diff < k2 and both are multiples of k1 => diff + k1 <= k2
    // Proof by contradiction: if diff + k1 > k2, then (q1-q2) >= qk,
    // so diff >= qk * k1 = k2, contradicting diff < k2.
    if q1 - q2 >= qk {
        // (q1-q2)*k1 >= qk*k1 = k2 > diff. Contradiction.
        lemma_mul_inequality(qk, q1 - q2, k1 as int);
        lemma_mul_is_commutative(k1 as int, q1 - q2);
    } else {
        // q1-q2 < qk, so q1-q2+1 <= qk
        // (q1-q2+1)*k1 <= qk*k1 = k2, i.e., diff + k1 <= k2
        lemma_mul_inequality(q1 - q2 + 1, qk, k1 as int);
        lemma_mul_is_commutative(k1 as int, q1 - q2 + 1);
        lemma_mul_is_distributive_add(k1 as int, q1 - q2, 1 as int);
        lemma_mul_is_commutative(k1 as int, q1 - q2);
    }
}

broadcast group group_arithmetic_lemmas {
    lemma_nat_align_up_sound,
    lemma_nat_align_down_sound,
}

} // verus!
