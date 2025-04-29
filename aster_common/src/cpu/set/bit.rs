use vstd::prelude::*;

verus! {

pub open spec fn bit_full_spec() -> nat {
    u64::MAX as nat
}

const fn bit_full() -> (res: u64)
    ensures
        res == bit_full_spec(),
{
    u64::MAX
}

pub open spec fn bit_reverse_spec(val: nat) -> nat {
    (bit_full_spec() - val) as nat
}

const fn bit_reverse(val: u64) -> (res: u64)
    ensures
        res == bit_reverse_spec(val as nat),
{
    bit_full() - val
}

pub open spec fn bit_and_spec(x: nat, y: nat) -> nat {
    (x as u64 & y as u64) as nat
}

const fn bit_and(x: u64, y: u64) -> (res: u64)
    ensures
        res == bit_and_spec(x as nat, y as nat),
{
    x & y
}

} // verus!
