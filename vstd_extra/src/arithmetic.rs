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
        forall|n: nat|
            #![trigger trigger(n)]
            n >= x && n % align == 0 ==> n >= nat_align_up(x, align),
{
    admit();
}

pub broadcast proof fn lemma_nat_align_down_sound(x: nat, align: nat)
    requires
        align > 0,
    ensures
        #[trigger] nat_align_down(x, align) <= x,
        nat_align_down(x, align) % align == 0,
        forall|n: nat|
            #![trigger trigger(n)]
            n <= x && n % align == 0 ==> n <= #[trigger] nat_align_down(x, align),
{
    admit();
}

broadcast group group_arithmetic_lemmas {
    lemma_nat_align_up_sound,
    lemma_nat_align_down_sound,
}

} // verus!
