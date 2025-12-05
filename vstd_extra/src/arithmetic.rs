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
        forall|n: nat|  n >= x && #[trigger] (n % align) == 0 ==> n >= nat_align_up(x, align),
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

    assert forall|n: nat| n >= x && (#[trigger] (n % align))== 0 implies n >= nat_align_up(
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

broadcast group group_arithmetic_lemmas {
    lemma_nat_align_up_sound,
    lemma_nat_align_down_sound,
}

} // verus!
