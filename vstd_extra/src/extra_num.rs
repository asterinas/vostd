use vstd::prelude::*;
use vstd::arithmetic::logarithm::*;
use vstd::arithmetic::power2::*;
use vstd::arithmetic::power::*;
use vstd::bits::*;
use vstd::layout::is_power_2;

verus! {

pub broadcast proof fn lemma_pow2_log2(e: nat)
    ensures
        #[trigger] log(2, pow2(e) as int) == e,
{
    lemma_pow2(e);
    lemma_log_pow(2, e);
}

pub broadcast proof fn lemma_pow2_increases(e1: nat, e2: nat)
    requires
        e1 <= e2,
    ensures
        #[trigger] pow2(e1) <= #[trigger] pow2(e2),
{
    if e1 < e2 {
        lemma_pow2_strictly_increases(e1, e2);
    } else if e1 == e2 {
        assert(pow2(e1) == pow2(e2));
    }
}

pub broadcast proof fn lemma_pow2_is_power2(e: nat)
    ensures
        #[trigger] is_power_2(pow2(e) as int),
    decreases e,
{
    if e == 0 {
        assert(pow2(e) == 1) by {
            lemma2_to64();
        };
        assert(is_power_2(1));
    } else {
        lemma_pow2_is_power2((e - 1) as nat);
        let p = pow2((e - 1) as nat) as int;
        assert(is_power_2(p));
        assert(pow2(e) == 2 * p) by {
            lemma_pow2_unfold(e);
        };
        assert(pow2(e) % 2 == 0);
        assert(is_power_2(2 * p / 2));
        assert(is_power_2(p));
    }
}

pub proof fn lemma_is_power2_exists_pow2(e: nat)
    requires
        is_power_2(e as int),
    ensures
        exists|n: nat| pow2(n) == e,
    decreases e,
{
    if e == 0 {
    } else if e == 1 {
        assert(pow2(0) == 1) by {
            lemma2_to64();
        };
    } else {
        lemma_is_power2_exists_pow2(e / 2);
        let n = choose|n: nat| pow2(n) == e / 2;
        assert(pow2(n + 1) == e) by {
            lemma_pow2_unfold(n + 1);
        }
    }
}

pub proof fn lemma2_to64_hi32()
    ensures
        pow2(33) == 0x200000000,
        pow2(34) == 0x400000000,
        pow2(35) == 0x800000000,
        pow2(36) == 0x1000000000,
        pow2(37) == 0x2000000000,
        pow2(38) == 0x4000000000,
        pow2(39) == 0x8000000000,
        pow2(40) == 0x10000000000,
        pow2(41) == 0x20000000000,
        pow2(42) == 0x40000000000,
        pow2(43) == 0x80000000000,
        pow2(44) == 0x100000000000,
        pow2(45) == 0x200000000000,
        pow2(46) == 0x400000000000,
        pow2(47) == 0x800000000000,
        pow2(48) == 0x1000000000000,
        pow2(49) == 0x2000000000000,
        pow2(50) == 0x4000000000000,
        pow2(51) == 0x8000000000000,
        pow2(52) == 0x10000000000000,
        pow2(53) == 0x20000000000000,
        pow2(54) == 0x40000000000000,
        pow2(55) == 0x80000000000000,
        pow2(56) == 0x100000000000000,
        pow2(57) == 0x200000000000000,
        pow2(58) == 0x400000000000000,
        pow2(59) == 0x800000000000000,
        pow2(60) == 0x1000000000000000,
        pow2(61) == 0x2000000000000000,
        pow2(62) == 0x4000000000000000,
        pow2(63) == 0x8000000000000000,
        pow2(64) == 0x10000000000000000,
{
    lemma2_to64();
    reveal(pow2);
    reveal(pow);
    #[verusfmt::skip]
    assert(
        pow2(33) == 0x200000000 &&
        pow2(34) == 0x400000000 &&
        pow2(35) == 0x800000000 &&
        pow2(36) == 0x1000000000 &&
        pow2(37) == 0x2000000000 &&
        pow2(38) == 0x4000000000 &&
        pow2(39) == 0x8000000000 &&
        pow2(40) == 0x10000000000 &&
        pow2(41) == 0x20000000000 &&
        pow2(42) == 0x40000000000 &&
        pow2(43) == 0x80000000000 &&
        pow2(44) == 0x100000000000 &&
        pow2(45) == 0x200000000000 &&
        pow2(46) == 0x400000000000 &&
        pow2(47) == 0x800000000000 &&
        pow2(48) == 0x1000000000000 &&
        pow2(49) == 0x2000000000000 &&
        pow2(50) == 0x4000000000000 &&
        pow2(51) == 0x8000000000000 &&
        pow2(52) == 0x10000000000000 &&
        pow2(53) == 0x20000000000000 &&
        pow2(54) == 0x40000000000000 &&
        pow2(55) == 0x80000000000000 &&
        pow2(56) == 0x100000000000000 &&
        pow2(57) == 0x200000000000000 &&
        pow2(58) == 0x400000000000000 &&
        pow2(59) == 0x800000000000000 &&
        pow2(60) == 0x1000000000000000 &&
        pow2(61) == 0x2000000000000000 &&
        pow2(62) == 0x4000000000000000 &&
        pow2(63) == 0x8000000000000000 &&
        pow2(64) == 0x10000000000000000
    ) by (compute_only);
}

pub proof fn lemma_pow2_is_power2_to64()
    ensures
        is_power_2(0x1),
        is_power_2(0x2),
        is_power_2(0x4),
        is_power_2(0x8),
        is_power_2(0x10),
        is_power_2(0x20),
        is_power_2(0x40),
        is_power_2(0x80),
        is_power_2(0x100),
        is_power_2(0x200),
        is_power_2(0x400),
        is_power_2(0x800),
        is_power_2(0x1000),
        is_power_2(0x2000),
        is_power_2(0x4000),
        is_power_2(0x8000),
        is_power_2(0x10000),
        is_power_2(0x20000),
        is_power_2(0x40000),
        is_power_2(0x80000),
        is_power_2(0x100000),
        is_power_2(0x200000),
        is_power_2(0x400000),
        is_power_2(0x800000),
        is_power_2(0x1000000),
        is_power_2(0x2000000),
        is_power_2(0x4000000),
        is_power_2(0x8000000),
        is_power_2(0x10000000),
        is_power_2(0x20000000),
        is_power_2(0x40000000),
        is_power_2(0x80000000),
        is_power_2(0x100000000),
        is_power_2(0x200000000),
        is_power_2(0x400000000),
        is_power_2(0x800000000),
        is_power_2(0x1000000000),
        is_power_2(0x2000000000),
        is_power_2(0x4000000000),
        is_power_2(0x8000000000),
        is_power_2(0x10000000000),
        is_power_2(0x20000000000),
        is_power_2(0x40000000000),
        is_power_2(0x80000000000),
        is_power_2(0x100000000000),
        is_power_2(0x200000000000),
        is_power_2(0x400000000000),
        is_power_2(0x800000000000),
        is_power_2(0x1000000000000),
        is_power_2(0x2000000000000),
        is_power_2(0x4000000000000),
        is_power_2(0x8000000000000),
        is_power_2(0x10000000000000),
        is_power_2(0x20000000000000),
        is_power_2(0x40000000000000),
        is_power_2(0x80000000000000),
        is_power_2(0x100000000000000),
        is_power_2(0x200000000000000),
        is_power_2(0x400000000000000),
        is_power_2(0x800000000000000),
        is_power_2(0x1000000000000000),
        is_power_2(0x2000000000000000),
        is_power_2(0x4000000000000000),
        is_power_2(0x8000000000000000),
        is_power_2(0x10000000000000000),
{
    lemma2_to64();
    lemma2_to64_hi32();
    lemma_pow2_is_power2(0);
    lemma_pow2_is_power2(1);
    lemma_pow2_is_power2(2);
    lemma_pow2_is_power2(3);
    lemma_pow2_is_power2(4);
    lemma_pow2_is_power2(5);
    lemma_pow2_is_power2(6);
    lemma_pow2_is_power2(7);
    lemma_pow2_is_power2(8);
    lemma_pow2_is_power2(9);
    lemma_pow2_is_power2(10);
    lemma_pow2_is_power2(11);
    lemma_pow2_is_power2(12);
    lemma_pow2_is_power2(13);
    lemma_pow2_is_power2(14);
    lemma_pow2_is_power2(15);
    lemma_pow2_is_power2(16);
    lemma_pow2_is_power2(17);
    lemma_pow2_is_power2(18);
    lemma_pow2_is_power2(19);
    lemma_pow2_is_power2(20);
    lemma_pow2_is_power2(21);
    lemma_pow2_is_power2(22);
    lemma_pow2_is_power2(23);
    lemma_pow2_is_power2(24);
    lemma_pow2_is_power2(25);
    lemma_pow2_is_power2(26);
    lemma_pow2_is_power2(27);
    lemma_pow2_is_power2(28);
    lemma_pow2_is_power2(29);
    lemma_pow2_is_power2(30);
    lemma_pow2_is_power2(31);
    lemma_pow2_is_power2(32);
    lemma_pow2_is_power2(33);
    lemma_pow2_is_power2(34);
    lemma_pow2_is_power2(35);
    lemma_pow2_is_power2(36);
    lemma_pow2_is_power2(37);
    lemma_pow2_is_power2(38);
    lemma_pow2_is_power2(39);
    lemma_pow2_is_power2(40);
    lemma_pow2_is_power2(41);
    lemma_pow2_is_power2(42);
    lemma_pow2_is_power2(43);
    lemma_pow2_is_power2(44);
    lemma_pow2_is_power2(45);
    lemma_pow2_is_power2(46);
    lemma_pow2_is_power2(47);
    lemma_pow2_is_power2(48);
    lemma_pow2_is_power2(49);
    lemma_pow2_is_power2(50);
    lemma_pow2_is_power2(51);
    lemma_pow2_is_power2(52);
    lemma_pow2_is_power2(53);
    lemma_pow2_is_power2(54);
    lemma_pow2_is_power2(55);
    lemma_pow2_is_power2(56);
    lemma_pow2_is_power2(57);
    lemma_pow2_is_power2(58);
    lemma_pow2_is_power2(59);
    lemma_pow2_is_power2(60);
    lemma_pow2_is_power2(61);
    lemma_pow2_is_power2(62);
    lemma_pow2_is_power2(63);
    lemma_pow2_is_power2(64);
}

pub proof fn lemma_log2_to64()
    ensures
        log(2, 0x1) == 0,
        log(2, 0x2) == 1,
        log(2, 0x4) == 2,
        log(2, 0x8) == 3,
        log(2, 0x10) == 4,
        log(2, 0x20) == 5,
        log(2, 0x40) == 6,
        log(2, 0x80) == 7,
        log(2, 0x100) == 8,
        log(2, 0x200) == 9,
        log(2, 0x400) == 10,
        log(2, 0x800) == 11,
        log(2, 0x1000) == 12,
        log(2, 0x2000) == 13,
        log(2, 0x4000) == 14,
        log(2, 0x8000) == 15,
        log(2, 0x10000) == 16,
        log(2, 0x20000) == 17,
        log(2, 0x40000) == 18,
        log(2, 0x80000) == 19,
        log(2, 0x100000) == 20,
        log(2, 0x200000) == 21,
        log(2, 0x400000) == 22,
        log(2, 0x800000) == 23,
        log(2, 0x1000000) == 24,
        log(2, 0x2000000) == 25,
        log(2, 0x4000000) == 26,
        log(2, 0x8000000) == 27,
        log(2, 0x10000000) == 28,
        log(2, 0x20000000) == 29,
        log(2, 0x40000000) == 30,
        log(2, 0x80000000) == 31,
        log(2, 0x100000000) == 32,
        log(2, 0x200000000) == 33,
        log(2, 0x400000000) == 34,
        log(2, 0x800000000) == 35,
        log(2, 0x1000000000) == 36,
        log(2, 0x2000000000) == 37,
        log(2, 0x4000000000) == 38,
        log(2, 0x8000000000) == 39,
        log(2, 0x10000000000) == 40,
        log(2, 0x20000000000) == 41,
        log(2, 0x40000000000) == 42,
        log(2, 0x80000000000) == 43,
        log(2, 0x100000000000) == 44,
        log(2, 0x200000000000) == 45,
        log(2, 0x400000000000) == 46,
        log(2, 0x800000000000) == 47,
        log(2, 0x1000000000000) == 48,
        log(2, 0x2000000000000) == 49,
        log(2, 0x4000000000000) == 50,
        log(2, 0x8000000000000) == 51,
        log(2, 0x10000000000000) == 52,
        log(2, 0x20000000000000) == 53,
        log(2, 0x40000000000000) == 54,
        log(2, 0x80000000000000) == 55,
        log(2, 0x100000000000000) == 56,
        log(2, 0x200000000000000) == 57,
        log(2, 0x400000000000000) == 58,
        log(2, 0x800000000000000) == 59,
        log(2, 0x1000000000000000) == 60,
        log(2, 0x2000000000000000) == 61,
        log(2, 0x4000000000000000) == 62,
        log(2, 0x8000000000000000) == 63,
        log(2, 0x10000000000000000) == 64,
{
    lemma2_to64();
    lemma2_to64_hi32();
    lemma_pow2_log2(0);
    lemma_pow2_log2(1);
    lemma_pow2_log2(2);
    lemma_pow2_log2(3);
    lemma_pow2_log2(4);
    lemma_pow2_log2(5);
    lemma_pow2_log2(6);
    lemma_pow2_log2(7);
    lemma_pow2_log2(8);
    lemma_pow2_log2(9);
    lemma_pow2_log2(10);
    lemma_pow2_log2(11);
    lemma_pow2_log2(12);
    lemma_pow2_log2(13);
    lemma_pow2_log2(14);
    lemma_pow2_log2(15);
    lemma_pow2_log2(16);
    lemma_pow2_log2(17);
    lemma_pow2_log2(18);
    lemma_pow2_log2(19);
    lemma_pow2_log2(20);
    lemma_pow2_log2(21);
    lemma_pow2_log2(22);
    lemma_pow2_log2(23);
    lemma_pow2_log2(24);
    lemma_pow2_log2(25);
    lemma_pow2_log2(26);
    lemma_pow2_log2(27);
    lemma_pow2_log2(28);
    lemma_pow2_log2(29);
    lemma_pow2_log2(30);
    lemma_pow2_log2(31);
    lemma_pow2_log2(32);
    lemma_pow2_log2(33);
    lemma_pow2_log2(34);
    lemma_pow2_log2(35);
    lemma_pow2_log2(36);
    lemma_pow2_log2(37);
    lemma_pow2_log2(38);
    lemma_pow2_log2(39);
    lemma_pow2_log2(40);
    lemma_pow2_log2(41);
    lemma_pow2_log2(42);
    lemma_pow2_log2(43);
    lemma_pow2_log2(44);
    lemma_pow2_log2(45);
    lemma_pow2_log2(46);
    lemma_pow2_log2(47);
    lemma_pow2_log2(48);
    lemma_pow2_log2(49);
    lemma_pow2_log2(50);
    lemma_pow2_log2(51);
    lemma_pow2_log2(52);
    lemma_pow2_log2(53);
    lemma_pow2_log2(54);
    lemma_pow2_log2(55);
    lemma_pow2_log2(56);
    lemma_pow2_log2(57);
    lemma_pow2_log2(58);
    lemma_pow2_log2(59);
    lemma_pow2_log2(60);
    lemma_pow2_log2(61);
    lemma_pow2_log2(62);
    lemma_pow2_log2(63);
    lemma_pow2_log2(64);
}

} // verus!
macro_rules! impl_external_ilog2 {
    ($uN: ty, $spec_name: ident,
    $pow2_lemma: ident, $pow2_ilog2_lemma: ident,
    $log2_bounds_lemma: ident, $ilog2_ordered_lemma: ident, $is_power_2_is_ilog2_pow2_lemma: ident $(,)?) => {
        verus! {
            #[verifier::inline]
            pub open spec fn $spec_name(x: $uN) -> u32
            {
                log(2, x as int) as u32
            }

            #[verifier::when_used_as_spec($spec_name)]
            pub assume_specification[$uN::ilog2](x:$uN) -> u32
                requires
                    x > 0,
                returns
                    log(2, x as int) as u32,
                opens_invariants none
                no_unwind;

            pub broadcast proof fn $pow2_lemma(e: u32, x: $uN)
                requires
                    #[trigger] pow2(e as nat) == x,
                ensures
                    #[trigger] x.ilog2() == e,
            {
                lemma_pow2_log2(e as nat);
            }

            pub broadcast proof fn $pow2_ilog2_lemma(e: u32)
                requires
                    pow2(e as nat) <= $uN::MAX,
                ensures
                    #[trigger] (pow2(e as nat) as $uN).ilog2() == e,
            {
                $pow2_lemma(e, pow2(e as nat) as $uN);
            }

            pub proof fn $log2_bounds_lemma(x: $uN)
                ensures
                    0 <= log(2, x as int) <= $uN::BITS,
                    0 <= x.ilog2() <= $uN::BITS,
            {
                lemma_log_nonnegative(2, x as int);
                assert(x <= $uN::MAX);
                assert(($uN::MAX as int) < (pow2($uN::BITS as nat) as int)) by {
                    lemma2_to64();
                };
                assert(log(2, x as int) <= log(2, pow2($uN::BITS as nat) as int)) by {
                    lemma_log_is_ordered(2, x as int, pow2($uN::BITS as nat) as int);
                };
                assert(log(2, pow2($uN::BITS as nat) as int) == $uN::BITS) by {
                    lemma_pow2_log2($uN::BITS as nat);
                };
            }

            pub proof fn $ilog2_ordered_lemma(x: $uN, y: $uN)
                requires
                    x <= y,
                ensures
                    x.ilog2() <= y.ilog2(),
            {
                $log2_bounds_lemma(x);
                $log2_bounds_lemma(y);
                lemma_log_is_ordered(2, x as int, y as int);
            }

            pub broadcast proof fn $is_power_2_is_ilog2_pow2_lemma(x: $uN)
                requires
                    #[trigger] is_power_2(x as int),
                ensures
                    x as nat == pow2(x.ilog2() as nat),
            {
                lemma_is_power2_exists_pow2(x as nat);
                let n = choose |n: nat| pow2(n) == x as nat;
                assert(log(2, x as int) == n) by {
                    lemma_pow2_log2(n);
                };
                assert($uN::MAX as int + 1 == pow2($uN::BITS as nat) as int) by {
                    lemma2_to64();
                };
                lemma_pow2(n);
                lemma_pow2($uN::BITS as nat);
                assert(n <= $uN::BITS) by {
                    lemma_pow_increases_converse(2, n, $uN::BITS as nat);
                };
                assert(x.ilog2() == n);
            }
        }
    };
}

impl_external_ilog2!(
    u8,
    u8_ilog2_spec,
    lemma_u8_pow2_ilog2_x,
    lemma_u8_pow2_ilog2,
    lemma_u8_log2_bounds,
    lemma_u8_ilog2_ordered,
    lemma_u8_is_power_2_is_ilog2_pow2,
);

impl_external_ilog2!(
    u16,
    u16_ilog2_spec,
    lemma_u16_pow2_ilog2_x,
    lemma_u16_pow2_ilog2,
    lemma_u16_log2_bounds,
    lemma_u16_ilog2_ordered,
    lemma_u16_is_power_2_is_ilog2_pow2,
);

impl_external_ilog2!(
    u32,
    u32_ilog2_spec,
    lemma_u32_pow2_ilog2_x,
    lemma_u32_pow2_ilog2,
    lemma_u32_log2_bounds,
    lemma_u32_ilog2_ordered,
    lemma_u32_is_power_2_is_ilog2_pow2,
);

impl_external_ilog2!(
    usize,
    usize_ilog2_spec,
    lemma_usize_pow2_ilog2_x,
    lemma_usize_pow2_ilog2,
    lemma_usize_log2_bounds,
    lemma_usize_ilog2_ordered,
    lemma_usize_is_power_2_is_ilog2_pow2,
);

impl_external_ilog2!(
    u64,
    u64_ilog2_spec,
    lemma_u64_pow2_ilog2_x,
    lemma_u64_pow2_ilog2,
    lemma_u64_log2_bounds,
    lemma_u64_ilog2_ordered,
    lemma_u64_is_power_2_is_ilog2_pow2,
);

verus! {

pub proof fn lemma_u8_ilog2_to8()
    ensures
        (0x1 as u8).ilog2() == 0,
        (0x2 as u8).ilog2() == 1,
        (0x4 as u8).ilog2() == 2,
        (0x8 as u8).ilog2() == 3,
        (0x10 as u8).ilog2() == 4,
        (0x20 as u8).ilog2() == 5,
        (0x40 as u8).ilog2() == 6,
        (0x80 as u8).ilog2() == 7,
{
    lemma_log2_to64();
}

pub proof fn lemma_u16_ilog2_to16()
    ensures
        (0x1 as u16).ilog2() == 0,
        (0x2 as u16).ilog2() == 1,
        (0x4 as u16).ilog2() == 2,
        (0x8 as u16).ilog2() == 3,
        (0x10 as u16).ilog2() == 4,
        (0x20 as u16).ilog2() == 5,
        (0x40 as u16).ilog2() == 6,
        (0x80 as u16).ilog2() == 7,
        (0x100 as u16).ilog2() == 8,
        (0x200 as u16).ilog2() == 9,
        (0x400 as u16).ilog2() == 10,
        (0x800 as u16).ilog2() == 11,
        (0x1000 as u16).ilog2() == 12,
        (0x2000 as u16).ilog2() == 13,
        (0x4000 as u16).ilog2() == 14,
        (0x8000 as u16).ilog2() == 15,
{
    lemma_log2_to64();
}

pub proof fn lemma_u32_ilog2_to32()
    ensures
        (0x1 as u32).ilog2() == 0,
        (0x2 as u32).ilog2() == 1,
        (0x4 as u32).ilog2() == 2,
        (0x8 as u32).ilog2() == 3,
        (0x10 as u32).ilog2() == 4,
        (0x20 as u32).ilog2() == 5,
        (0x40 as u32).ilog2() == 6,
        (0x80 as u32).ilog2() == 7,
        (0x100 as u32).ilog2() == 8,
        (0x200 as u32).ilog2() == 9,
        (0x400 as u32).ilog2() == 10,
        (0x800 as u32).ilog2() == 11,
        (0x1000 as u32).ilog2() == 12,
        (0x2000 as u32).ilog2() == 13,
        (0x4000 as u32).ilog2() == 14,
        (0x8000 as u32).ilog2() == 15,
        (0x10000 as u32).ilog2() == 16,
        (0x20000 as u32).ilog2() == 17,
        (0x40000 as u32).ilog2() == 18,
        (0x80000 as u32).ilog2() == 19,
        (0x100000 as u32).ilog2() == 20,
        (0x200000 as u32).ilog2() == 21,
        (0x400000 as u32).ilog2() == 22,
        (0x800000 as u32).ilog2() == 23,
        (0x1000000 as u32).ilog2() == 24,
        (0x2000000 as u32).ilog2() == 25,
        (0x4000000 as u32).ilog2() == 26,
        (0x8000000 as u32).ilog2() == 27,
        (0x10000000 as u32).ilog2() == 28,
        (0x20000000 as u32).ilog2() == 29,
        (0x40000000 as u32).ilog2() == 30,
        (0x80000000 as u32).ilog2() == 31,
{
    lemma_log2_to64();
}

pub proof fn lemma_usize_ilog2_to32()
    ensures
        (0x1 as usize).ilog2() == 0,
        (0x2 as usize).ilog2() == 1,
        (0x4 as usize).ilog2() == 2,
        (0x8 as usize).ilog2() == 3,
        (0x10 as usize).ilog2() == 4,
        (0x20 as usize).ilog2() == 5,
        (0x40 as usize).ilog2() == 6,
        (0x80 as usize).ilog2() == 7,
        (0x100 as usize).ilog2() == 8,
        (0x200 as usize).ilog2() == 9,
        (0x400 as usize).ilog2() == 10,
        (0x800 as usize).ilog2() == 11,
        (0x1000 as usize).ilog2() == 12,
        (0x2000 as usize).ilog2() == 13,
        (0x4000 as usize).ilog2() == 14,
        (0x8000 as usize).ilog2() == 15,
        (0x10000 as usize).ilog2() == 16,
        (0x20000 as usize).ilog2() == 17,
        (0x40000 as usize).ilog2() == 18,
        (0x80000 as usize).ilog2() == 19,
        (0x100000 as usize).ilog2() == 20,
        (0x200000 as usize).ilog2() == 21,
        (0x400000 as usize).ilog2() == 22,
        (0x800000 as usize).ilog2() == 23,
        (0x1000000 as usize).ilog2() == 24,
        (0x2000000 as usize).ilog2() == 25,
        (0x4000000 as usize).ilog2() == 26,
        (0x8000000 as usize).ilog2() == 27,
        (0x10000000 as usize).ilog2() == 28,
        (0x20000000 as usize).ilog2() == 29,
        (0x40000000 as usize).ilog2() == 30,
        (0x80000000 as usize).ilog2() == 31,
{
    lemma_log2_to64();
}

pub proof fn lemma_u64_ilog2_to64()
    ensures
        (0x1 as u64).ilog2() == 0,
        (0x2 as u64).ilog2() == 1,
        (0x4 as u64).ilog2() == 2,
        (0x8 as u64).ilog2() == 3,
        (0x10 as u64).ilog2() == 4,
        (0x20 as u64).ilog2() == 5,
        (0x40 as u64).ilog2() == 6,
        (0x80 as u64).ilog2() == 7,
        (0x100 as u64).ilog2() == 8,
        (0x200 as u64).ilog2() == 9,
        (0x400 as u64).ilog2() == 10,
        (0x800 as u64).ilog2() == 11,
        (0x1000 as u64).ilog2() == 12,
        (0x2000 as u64).ilog2() == 13,
        (0x4000 as u64).ilog2() == 14,
        (0x8000 as u64).ilog2() == 15,
        (0x10000 as u64).ilog2() == 16,
        (0x20000 as u64).ilog2() == 17,
        (0x40000 as u64).ilog2() == 18,
        (0x80000 as u64).ilog2() == 19,
        (0x100000 as u64).ilog2() == 20,
        (0x200000 as u64).ilog2() == 21,
        (0x400000 as u64).ilog2() == 22,
        (0x800000 as u64).ilog2() == 23,
        (0x1000000 as u64).ilog2() == 24,
        (0x2000000 as u64).ilog2() == 25,
        (0x4000000 as u64).ilog2() == 26,
        (0x8000000 as u64).ilog2() == 27,
        (0x10000000 as u64).ilog2() == 28,
        (0x20000000 as u64).ilog2() == 29,
        (0x40000000 as u64).ilog2() == 30,
        (0x80000000 as u64).ilog2() == 31,
        (0x100000000 as u64).ilog2() == 32,
        (0x200000000 as u64).ilog2() == 33,
        (0x400000000 as u64).ilog2() == 34,
        (0x800000000 as u64).ilog2() == 35,
        (0x1000000000 as u64).ilog2() == 36,
        (0x2000000000 as u64).ilog2() == 37,
        (0x4000000000 as u64).ilog2() == 38,
        (0x8000000000 as u64).ilog2() == 39,
        (0x10000000000 as u64).ilog2() == 40,
        (0x20000000000 as u64).ilog2() == 41,
        (0x40000000000 as u64).ilog2() == 42,
        (0x80000000000 as u64).ilog2() == 43,
        (0x100000000000 as u64).ilog2() == 44,
        (0x200000000000 as u64).ilog2() == 45,
        (0x400000000000 as u64).ilog2() == 46,
        (0x800000000000 as u64).ilog2() == 47,
        (0x1000000000000 as u64).ilog2() == 48,
        (0x2000000000000 as u64).ilog2() == 49,
        (0x4000000000000 as u64).ilog2() == 50,
        (0x8000000000000 as u64).ilog2() == 51,
        (0x10000000000000 as u64).ilog2() == 52,
        (0x20000000000000 as u64).ilog2() == 53,
        (0x40000000000000 as u64).ilog2() == 54,
        (0x80000000000000 as u64).ilog2() == 55,
        (0x100000000000000 as u64).ilog2() == 56,
        (0x200000000000000 as u64).ilog2() == 57,
        (0x400000000000000 as u64).ilog2() == 58,
        (0x800000000000000 as u64).ilog2() == 59,
        (0x1000000000000000 as u64).ilog2() == 60,
        (0x2000000000000000 as u64).ilog2() == 61,
        (0x4000000000000000 as u64).ilog2() == 62,
        (0x8000000000000000 as u64).ilog2() == 63,
{
    lemma_log2_to64();
}

pub broadcast proof fn lemma_usize_shl_is_mul(x: usize, shift: usize)
    requires
        0 <= shift < usize::BITS,
        x * pow2(shift as nat) <= usize::MAX,
    ensures
        #[trigger] (x << shift) == x * pow2(shift as nat),
{
    if usize::BITS == 64 {
        lemma_u64_shl_is_mul(x as u64, shift as u64);
    } else if usize::BITS == 32 {
        lemma_u32_shl_is_mul(x as u32, shift as u32);
    } else {
        assert(false);
    }
}

pub broadcast proof fn lemma_usize_pow2_shl_is_pow2(x: usize, shift: usize)
    requires
        0 <= shift < usize::BITS,
        is_power_2(x as int),
        x * pow2(shift as nat) <= usize::MAX,
    ensures
        #[trigger] is_power_2((x << shift) as int),
{
    lemma_is_power2_exists_pow2(x as nat);
    let n = choose|n: nat| pow2(n) == x as nat;
    lemma_usize_shl_is_mul(x, shift);
    assert(x << shift == x * pow2(shift as nat));
    lemma_pow2_adds(n, shift as nat);
    assert(x * pow2(shift as nat) == pow2(n + shift as nat));
    lemma_pow2_is_power2(n + shift as nat);
    assert(is_power_2((x << shift) as int));
}

} // verus!
