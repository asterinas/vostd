// SPDX-License-Identifier: MPL-2.0
use vstd::{
    bits,
    prelude::*,
    raw_ptr::group_raw_ptr_axioms,
    std_specs::{nonzero::*, ops::BitOrSpec},
};
use vstd_extra::{prelude::*, sum::Sum};

use super::NonNullPtr;
use crate::util::Either;
use core::num::NonZeroUsize;
use core::{marker::PhantomData, ptr::NonNull};

verus! {

broadcast use {group_nonull_axioms, group_nonzero_axioms, group_raw_ptr_axioms};
// If both `L` and `R` have at least one alignment bit (i.e., their alignments are at least 2), we
// can use the alignment bit to indicate whether a pointer is `L` or `R`, so it's possible to
// implement `NonNullPtr` for `Either<L, R>`.

unsafe impl<L: NonNullPtr, R: NonNullPtr> NonNullPtr for Either<L, R> {
    type Target = PhantomData<Self>;

    type Permission = Sum<L::Permission, R::Permission>;

    type Ref<'a> = Either<L::Ref<'a>, R::Ref<'a>>;

    type RefPermission<'a> = Sum<L::RefPermission<'a>, R::RefPermission<'a>>;

    #[verifier::external_body]
    const ALIGN_BITS: u32 = min(L::ALIGN_BITS, R::ALIGN_BITS).checked_sub(1).expect(
        "`L` and `R` alignments should be at least 2 to pack `Either` into one pointer",
    );

    open spec fn align_bits_inv() -> bool {
        Self::ALIGN_BITS == if L::ALIGN_BITS < R::ALIGN_BITS {
            L::ALIGN_BITS - 1
        } else {
            R::ALIGN_BITS - 1
        }
    }

    #[verifier::spinoff_prover]
    fn into_raw(self) -> (ret: (NonNull<Self::Target>, Tracked<Self::Permission>)) {
        proof_decl!{
           let ghost align_bits = Self::ALIGN_BITS;
           let ghost l_align_bits = L::ALIGN_BITS;
           let ghost r_align_bits = R::ALIGN_BITS;
           let ghost tag = 1usize << align_bits;
        }
        proof! {
            L::lemma_align_bits_properties();
            R::lemma_align_bits_properties();
            Self::lemma_align_bits_properties();
            vstd::bits::lemma_usize_pow2_no_overflow(align_bits as nat);
            vstd::bits::lemma_usize_pow2_no_overflow(l_align_bits as nat);
            vstd::bits::lemma_usize_pow2_no_overflow(r_align_bits as nat);
            vstd::bits::lemma_usize_shl_is_mul(1, align_bits as usize);
            vstd::bits::lemma_usize_shl_is_mul(1, l_align_bits as usize);
            vstd::bits::lemma_usize_shl_is_mul(1, r_align_bits as usize);
        }
        match self {
            Self::Left(left) => {
                // left.into_raw().cast(),
                let (left, Tracked(perm)) = left.into_raw();
                proof! {
                    let left_addr = left.cast::<Self::Target>().as_ptr().addr();
                    let extra_bits: u32 = (l_align_bits - align_bits) as u32;
                    let scale = 1usize << extra_bits;
                    vstd::bits::lemma_usize_pow2_no_overflow(extra_bits as nat);
                    vstd::bits::lemma_usize_shl_is_mul(1, extra_bits as usize);
                    vstd::arithmetic::power2::lemma_pow2_adds(align_bits as nat, extra_bits as nat);
                    assert(left_addr % tag == 0) by {
                        let big = 1usize << l_align_bits;
                        let q = left_addr / big;
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(left_addr as int, big as int);
                        assert(left_addr % big == 0);
                        assert(left_addr == q * big);
                        assert(left_addr == q * scale * tag) by (nonlinear_arith)
                        requires
                            left_addr == q * big,
                            big == tag * scale,
                        ;
                        vstd::arithmetic::div_mod::lemma_mod_multiples_basic(q * scale, tag as int);
                    };
                    lemma_aligned_addr_clears_tag_bit(left_addr, tag, align_bits, l_align_bits);
                }
                (left.cast(), Tracked(Sum::Left(perm)))
            },
            Self::Right(right) => {
                /* right
                .into_raw()
                .map_addr(|addr| addr | (1 << Self::ALIGN_BITS))
                .cast(), */
                let (right, Tracked(perm)) = right.into_raw();
                let right_tagged = right.map_addr(
                    |addr: NonZeroUsize| -> (ret: NonZeroUsize)
                        ensures
                            ret@ == addr@ | (1usize << Self::ALIGN_BITS),
                        {
                            proof {
                                let tag = 1usize << Self::ALIGN_BITS;
                                let a = addr@;
                                assert(a | tag != 0) by (bit_vector)
                                    requires
                                        a != 0,
                                ;
                            }
                            addr | 1usize << Self::ALIGN_BITS
                        },
                );
                proof! {
                    let addr = right.addr_spec()@;
                    let tagged_addr = right_tagged.addr_spec()@;
                    lemma_aligned_addr_clears_tag_bit(addr, tag, align_bits, r_align_bits);
                    assert(tagged_addr & tag == tag) by (bit_vector)
                    requires
                        tagged_addr == addr | tag,
                    ;
                    let extra_bits: u32 = (r_align_bits - align_bits) as u32;
                    let scale = 1usize << extra_bits;
                    vstd::bits::lemma_usize_pow2_no_overflow(extra_bits as nat);
                    vstd::bits::lemma_usize_shl_is_mul(1, extra_bits as usize);
                    vstd::arithmetic::power2::lemma_pow2_adds(align_bits as nat, extra_bits as nat);
                    assert(tagged_addr == addr + tag) by (bit_vector)
                    requires
                        tagged_addr == addr | tag,
                        addr & tag == 0,
                    ;
                    assert(addr % tag == 0) by {
                        let big = 1usize << r_align_bits;
                        let q = addr / big;
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(addr as int, big as int);
                        assert(addr == q * scale * tag) by (nonlinear_arith)
                        requires
                            addr == q * big,
                            big == tag * scale,
                        ;
                        vstd::arithmetic::div_mod::lemma_mod_multiples_basic(q * scale, tag as int);
                    }
                    lemma_aligned_addr_clears_tag_bit(addr, tag, align_bits, r_align_bits);
                    assert(tagged_addr & !tag == addr) by (bit_vector)
                    requires
                        tagged_addr == addr | tag,
                        addr & tag == 0,
                    ;
                    assert(tagged_addr % (1usize << align_bits) == 0) by {
                        vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(addr as int, tag as int);
                    }
                }
                (right_tagged.cast(), Tracked(Sum::Right(perm)))
            },
        }
    }

    unsafe fn from_raw(
        ptr: NonNull<Self::Target>,
        Tracked(perm): Tracked<Self::Permission>,
    ) -> Self {
        proof! {
            Self::lemma_align_bits_properties();
        }
        proof_decl! {
            let ghost align_bits = Self::ALIGN_BITS;
            let ghost tag = 1usize << Self::ALIGN_BITS;
            let ghost ptr_addr = ptr.as_ptr()@.addr;
        }
        proof! {
            assert(tag > 0) by (bit_vector)
            requires
                tag == 1usize << align_bits,
                align_bits < usize::BITS,
            ;
            match perm {
                Sum::Left(_) => {
                    assert((ptr_addr & !tag) == ptr_addr) by (bit_vector)
                    requires
                        ptr_addr & tag == 0,
                    ;
                },
                Sum::Right(_) => {
                    assert((ptr_addr & tag) < ptr_addr) by (bit_vector)
                    requires
                        ptr_addr & tag == tag,
                        (ptr_addr & !tag) != 0,
                    ;
                },
            }
        }
        // SAFETY: The caller ensures that the pointer comes from `Self::into_raw`, which
        // guarantees that `real_ptr` is a non-null pointer.
        let (is_right, real_ptr) = unsafe { remove_bits(ptr, 1 << Self::ALIGN_BITS) };

        if is_right == 0 {
            // SAFETY: `Self::into_raw` guarantees that `real_ptr` comes from `L::into_raw`. Other
            // safety requirements are upheld by the caller.
            Either::Left(unsafe { L::from_raw(real_ptr.cast(), Tracked(perm.tracked_take_left())) })
        } else {
            // SAFETY: `Self::into_raw` guarantees that `real_ptr` comes from `R::into_raw`. Other
            // safety requirements are upheld by the caller.
            Either::Right(
                unsafe { R::from_raw(real_ptr.cast(), Tracked(perm.tracked_take_right())) },
            )
        }
    }

    open spec fn ptr_perm_match(ptr: *mut Self::Target, perm: Self::Permission) -> bool {
        let tag = 1usize << Self::ALIGN_BITS;
        match perm {
            Sum::Left(left) => {
                &&& ptr.addr() & tag == 0
                &&& L::ptr_perm_match(ptr.cast(), left)
            },
            Sum::Right(right) => {
                let untagged_ptr = ptr.with_addr((ptr.addr() & !tag));
                let right_nonnull = nonnull_from_ptr_mut_spec(untagged_ptr);
                &&& ptr.addr() & tag == tag
                &&& (ptr.addr() & !tag) != 0
                &&& R::ptr_perm_match(right_nonnull.cast().as_ptr(), right)
            },
        }
    }

    open spec fn rel_perm(self, perm: Self::Permission) -> bool {
        match (self, perm) {
            (Either::Left(left), Sum::Left(left_perm)) => left.rel_perm(left_perm),
            (Either::Right(right), Sum::Right(right_perm)) => right.rel_perm(right_perm),
            _ => false,
        }
    }

    axiom fn lemma_align_bits_properties();

    open spec fn ref_perm_view_permission<'a>(perm: Self::RefPermission<'a>) -> Self::Permission {
        match perm {
            Sum::Left(left) => Sum::Left(L::ref_perm_view_permission(left)),
            Sum::Right(right) => Sum::Right(R::ref_perm_view_permission(right)),
        }
    }

    open spec fn ref_rel_perm<'a>(r: Self::Ref<'a>, perm: Self::RefPermission<'a>) -> bool {
        match (r, perm) {
            (Either::Left(r), Sum::Left(perm)) => L::ref_rel_perm(r, perm),
            (Either::Right(r), Sum::Right(perm)) => R::ref_rel_perm(r, perm),
            _ => false,
        }
    }

    proof fn tracked_borrow_perm_as_ref_perm<'a>(
        tracked perm: &'a Self::Permission,
    ) -> tracked Self::RefPermission<'a> {
        if perm is Left {
            Sum::Left(L::tracked_borrow_perm_as_ref_perm(perm.tracked_borrow_left()))
        } else {
            Sum::Right(R::tracked_borrow_perm_as_ref_perm(perm.tracked_borrow_right()))
        }
    }

    unsafe fn raw_as_ref<'a>(
        raw: NonNull<Self::Target>,
        Tracked(perm): Tracked<Self::RefPermission<'a>>,
    ) -> Self::Ref<'a> {
        proof_decl! {
            let ghost align_bits = Self::ALIGN_BITS;
            let ghost tag = 1usize << align_bits;
            let ghost raw_addr = raw.as_ptr()@.addr;
        }
        proof! {
            Self::lemma_align_bits_properties();
            if perm is Left {
                assert((raw_addr & !tag) == raw_addr) by (bit_vector)
                    requires
                        raw_addr & tag == 0,
                    ;
            } else {
                assert((raw_addr & tag) < raw_addr) by (bit_vector)
                requires
                    raw_addr & tag == tag,
                    (raw_addr & !tag) != 0,
                ;
            }
        }
        // SAFETY: The caller ensures that the pointer comes from `Self::into_raw`, which
        // guarantees that `real_ptr` is a non-null pointer.
        let (is_right, real_ptr) = unsafe { remove_bits(raw, 1 << Self::ALIGN_BITS) };

        if is_right == 0 {
            proof!{
                if perm is Right {
                    assert(tag != 0) by (bit_vector)
                    requires
                        tag == 1usize << align_bits,
                        align_bits < usize::BITS,
                    ;
                    assert(false);
                }
            }
            // SAFETY: `Self::into_raw` guarantees that `real_ptr` comes from `L::into_raw`. Other
            // safety requirements are upheld by the caller.
            Either::Left(
                unsafe { L::raw_as_ref(real_ptr.cast(), Tracked(perm.tracked_take_left())) },
            )
        } else {
            // SAFETY: `Self::into_raw` guarantees that `real_ptr` comes from `R::into_raw`. Other
            // safety requirements are upheld by the caller.
            Either::Right(
                unsafe { R::raw_as_ref(real_ptr.cast(), Tracked(perm.tracked_take_right())) },
            )
        }
    }

    #[verifier::spinoff_prover]
    fn ref_as_raw<'a>(ptr_ref: Self::Ref<'a>) -> (
        NonNull<Self::Target>,
        Tracked<Self::RefPermission<'a>>,
    ) {
        proof!{
            Self::lemma_align_bits_properties();
        }
        proof_decl!{
            let ghost align_bits = Self::ALIGN_BITS;
            let ghost tag = 1usize << align_bits;
            let ghost l_align_bits = L::ALIGN_BITS;
            let ghost r_align_bits = R::ALIGN_BITS;
        }
        proof!{
            L::lemma_align_bits_properties();
            R::lemma_align_bits_properties();
            vstd::bits::lemma_usize_pow2_no_overflow(align_bits as nat);
            vstd::bits::lemma_usize_pow2_no_overflow(l_align_bits as nat);
            vstd::bits::lemma_usize_pow2_no_overflow(r_align_bits as nat);
            vstd::bits::lemma_usize_shl_is_mul(1, align_bits as usize);
            vstd::bits::lemma_usize_shl_is_mul(1, l_align_bits as usize);
            vstd::bits::lemma_usize_shl_is_mul(1, r_align_bits as usize);
        }
        match ptr_ref {
            Either::Left(left) => {
                // L::ref_as_raw(left).cast()
                let (ptr, Tracked(perm)) = L::ref_as_raw(left);
                proof! {
                    let ghost ptr_addr = ptr.as_ptr().addr();
                    let extra_bits: u32 = (l_align_bits - align_bits) as u32;
                    let scale = 1usize << extra_bits;
                    vstd::bits::lemma_usize_pow2_no_overflow(extra_bits as nat);
                    vstd::bits::lemma_usize_shl_is_mul(1, extra_bits as usize);
                    vstd::arithmetic::power2::lemma_pow2_adds(align_bits as nat, extra_bits as nat);
                    assert(ptr_addr % tag == 0) by {
                        let big = 1usize << l_align_bits;
                        let q = ptr_addr / big;
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ptr_addr as int, big as int);
                        assert(ptr_addr == (q * scale) * tag) by (nonlinear_arith)
                        requires
                            ptr_addr == q * big,
                            big == tag * scale,
                        ;
                        vstd::arithmetic::div_mod::lemma_mod_multiples_basic(q * scale, tag as int);
                    };
                    lemma_aligned_addr_clears_tag_bit(ptr_addr, tag, align_bits, l_align_bits);
                }
                (ptr.cast(), Tracked(Sum::Left(perm)))
            },
            Either::Right(right) => {
                /* R::ref_as_raw(right)
                .map_addr(|addr| addr | (1 << Self::ALIGN_BITS))
                .cast() */
                let (ptr, Tracked(perm)) = R::ref_as_raw(right);
                proof! {
                    Self::lemma_align_bits_properties();
                }
                let tagged_ptr = ptr.map_addr(
                    |addr: NonZeroUsize| -> (ret: NonZeroUsize)
                        ensures
                            ret@ == addr@ | (1usize << Self::ALIGN_BITS),
                        {
                            proof {
                                let tag = 1usize << Self::ALIGN_BITS;
                                let a = addr@;
                                assert(a | tag != 0) by (bit_vector)
                                    requires
                                        a != 0,
                                ;
                            }
                            addr | 1usize << Self::ALIGN_BITS
                        },
                );
                proof! {
                    let ghost ptr_addr = ptr.as_ptr().addr();
                    let ghost tagged_addr = tagged_ptr.as_ptr().addr();
                    assert(tagged_addr & tag == tag) by (bit_vector)
                    requires
                        tagged_addr == ptr_addr | tag,
                    ;
                    lemma_aligned_addr_clears_tag_bit(ptr_addr, tag, align_bits, r_align_bits);
                    assert(tagged_addr & !tag == ptr_addr) by (bit_vector)
                    requires
                        tagged_addr == ptr_addr | tag,
                        ptr_addr & tag == 0,
                    ;
                    let extra_bits: u32 = (r_align_bits - align_bits) as u32;
                    let scale = 1usize << extra_bits;
                    vstd::bits::lemma_usize_pow2_no_overflow(extra_bits as nat);
                    vstd::bits::lemma_usize_shl_is_mul(1, extra_bits as usize);
                    vstd::arithmetic::power2::lemma_pow2_adds(align_bits as nat, extra_bits as nat);
                    assert(tagged_addr == ptr_addr + tag) by (bit_vector)
                    requires
                        tagged_addr == ptr_addr | tag,
                        ptr_addr & tag == 0,
                    ;
                    assert(ptr_addr % tag == 0) by {
                        let big = 1usize << r_align_bits;
                        let q = ptr_addr / big;
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ptr_addr as int, big as int);
                        assert(ptr_addr == (q * scale) * tag) by (nonlinear_arith)
                        requires
                            ptr_addr == q * big,
                            big == tag * scale,
                        ;
                        vstd::arithmetic::div_mod::lemma_mod_multiples_basic(q * scale, tag as int);
                    };
                    assert(tagged_addr % tag == 0) by {
                        vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(ptr_addr as int, tag as int);
                    }
                }
                (tagged_ptr.cast(), Tracked(Sum::Right(perm)))
            },
        }
    }
}

} // verus!
// A `min` implementation for use in constant evaluation.
#[verus_verify(dual_spec)]
const fn min(a: u32, b: u32) -> u32 {
    if a < b { a } else { b }
}

verus! {

/// # Safety
///
/// The caller must ensure that removing the bits from the non-null pointer will result in another
/// non-null pointer.
// FIXEME: fix when verus attribute syntax supports closure postconditions.
#[verus_spec(ret =>
    requires
        (ptr.as_ptr().addr() & bits) < ptr.as_ptr().addr(),
        (ptr.as_ptr().addr() & !bits) != 0,
    ensures
        ret.0 == (ptr.as_ptr().addr() & bits),
        ret.1.as_ptr() == ptr.as_ptr().with_addr((ptr.as_ptr().addr() & !bits) as usize),
)]
unsafe fn remove_bits<T>(ptr: NonNull<T>, bits: usize) -> (usize, NonNull<T>) {
    use core::num::NonZeroUsize;

    let removed_bits = ptr.addr().get() & bits;
    let result_ptr = ptr.map_addr(
        |addr| -> (ret: NonZeroUsize)
            requires
                addr@ & !bits != 0,
            ensures
                ret@ == addr@ & !bits,
            {
                // SAFETY: The safety is upheld by the caller.
                unsafe { NonZeroUsize::new_unchecked(addr.get() & !bits) }
            },
    );
    (removed_bits, result_ptr)
}

#[verifier::spinoff_prover]
proof fn lemma_aligned_addr_clears_tag_bit(
    addr: usize,
    tag: usize,
    align_bits: u32,
    ptr_align_bits: u32,
)
    requires
        addr % (1usize << ptr_align_bits) == 0,
        tag == 1usize << align_bits,
        align_bits < ptr_align_bits < usize::BITS,
    ensures
        addr & tag == 0,
{
    assert(addr & (1usize << align_bits) == 0) by (bit_vector)
        requires
            addr % (1usize << ptr_align_bits) == 0,
            0u32 < ptr_align_bits,
            align_bits < ptr_align_bits,
            ptr_align_bits <= 63u32,
    ;
    assert(addr & tag == 0) by (bit_vector)
        requires
            addr & (1usize << align_bits) == 0,
            tag == 1usize << align_bits,
            align_bits < 64u32,
    ;
}

} // verus!
/* #[cfg(ktest)] */
mod test {
    use vstd::layout::layout_of_primitives;
    use vstd_extra::layout::lemma_primitive_layout;

    use alloc::{boxed::Box, sync::Arc};

    use super::*;
    /* use crate::{prelude::ktest, sync::RcuOption}; */
    use crate::sync::rcu::RcuOption;

    type Either32 = Either<Arc<u32>, Box<u32>>;
    type Either16 = Either<Arc<u32>, Box<u16>>;

    verus! {

broadcast use {
    group_nonull_axioms,
    group_nonzero_axioms,
    group_raw_ptr_axioms,
    layout_of_primitives,
};

} // verus!
    /* #[ktest] */
#[verus_spec]
    fn alignment() {
        proof! {
            lemma_primitive_layout();
            <Arc<u32> as NonNullPtr>::lemma_align_bits_properties();
            <Box<u32> as NonNullPtr>::lemma_align_bits_properties();
            <Box<u16> as NonNullPtr>::lemma_align_bits_properties();
            let box32_bits = <Box<u32> as NonNullPtr>::ALIGN_BITS;
            let box16_bits = <Box<u16> as NonNullPtr>::ALIGN_BITS;
            assert(box32_bits == 2) by (bit_vector)
                requires box32_bits < usize::BITS, 1usize << box32_bits == 4usize;
            assert(box16_bits == 1) by (bit_vector)
                requires box16_bits < usize::BITS, 1usize << box16_bits == 2usize;
            Either32::lemma_align_bits_properties();
            Either16::lemma_align_bits_properties();
        }
        assert_eq!(<Either32 as NonNullPtr>::ALIGN_BITS, 1);
        assert_eq!(<Either16 as NonNullPtr>::ALIGN_BITS, 0);
    }

    /* #[ktest] */
    #[verus_spec]
    fn left_pointer() {
        proof! {
            lemma_primitive_layout();
            <Arc<u32> as NonNullPtr>::lemma_align_bits_properties();
            <Box<u16> as NonNullPtr>::lemma_align_bits_properties();
            Either16::lemma_align_bits_properties();
            let right_bits = <Box<u16> as NonNullPtr>::ALIGN_BITS;
            assert(right_bits == 1) by (bit_vector)
                requires right_bits < usize::BITS, 1usize << right_bits == 2usize;
            let either_bits = Either16::ALIGN_BITS;
            assert(1usize << either_bits == 1usize) by (bit_vector)
                requires either_bits == 0;
        }
        let val: Either16 = Either::Left(Arc::new(123));

        /* Retain the ownership permission.
         * Origin Rust: let ptr = NonNullPtr::into_raw(val);
         */
        let (ptr, perm) = NonNullPtr::into_raw(val);
        assert_eq!(ptr.addr().get() & 1, 0);

        proof_decl! {
            let tracked ref_perm = <Either16 as NonNullPtr>::tracked_borrow_perm_as_ref_perm(perm.borrow());
        }
        /* Pass the borrowed permission.
         * Origin Rust: let ref_ = unsafe { <Either16 as NonNullPtr>::raw_as_ref(ptr) };
         */
        let ref_ = unsafe {
            verus_exec_expr! { <Either16 as NonNullPtr>::raw_as_ref(ptr, Tracked(ref_perm)) }
        };
        assert!(matches!(ref_, Either::Left(ref r) if ***r == 123));

        /* Receive the reading permission.
         * Origin Rust: let ptr2 = <Either16 as NonNullPtr>::ref_as_raw(ref_);
         */
        let (ptr2, _) = <Either16 as NonNullPtr>::ref_as_raw(ref_);
        // Arc's value model cannot prove allocation identity; keep the runtime check.
        #[cfg(all(ktest, not(verus_keep_ghost_body)))]
        assert_eq!(ptr, ptr2);

        /* Consume the ownership permission.
         * Origin Rust: let val = unsafe { <Either16 as NonNullPtr>::from_raw(ptr) };
         */
        let val = unsafe { <Either16 as NonNullPtr>::from_raw(ptr, perm) };
        assert!(matches!(val, Either::Left(ref r) if **r == 123));
        /* Unsupported explicit drop; use the same scope-exit drop.
         * Origin Rust: drop(val);
         */
    }

    /* #[ktest] */
    #[verus_spec]
    fn right_pointer() {
        proof! {
            lemma_primitive_layout();
            <Arc<u32> as NonNullPtr>::lemma_align_bits_properties();
            <Box<u16> as NonNullPtr>::lemma_align_bits_properties();
            Either16::lemma_align_bits_properties();
            let right_bits = <Box<u16> as NonNullPtr>::ALIGN_BITS;
            assert(right_bits == 1) by (bit_vector)
                requires right_bits < usize::BITS, 1usize << right_bits == 2usize;
            let either_bits = Either16::ALIGN_BITS;
            assert(1usize << either_bits == 1usize) by (bit_vector)
                requires either_bits == 0;
        }
        let val: Either16 = Either::Right(Box::new(456));

        /* Retain the ownership permission.
         * Origin Rust: let ptr = NonNullPtr::into_raw(val);
         */
        let (ptr, perm) = NonNullPtr::into_raw(val);
        assert_eq!(ptr.addr().get() & 1, 1);

        proof_decl! {
            let tracked ref_perm = <Either16 as NonNullPtr>::tracked_borrow_perm_as_ref_perm(perm.borrow());
        }
        /* Pass the borrowed permission.
         * Origin Rust: let ref_ = unsafe { <Either16 as NonNullPtr>::raw_as_ref(ptr) };
         */
        let ref_ = unsafe {
            verus_exec_expr! { <Either16 as NonNullPtr>::raw_as_ref(ptr, Tracked(ref_perm)) }
        };
        /* Use deref_target instead of the unsupported transmute-based Deref.
         * Origin Rust: assert!(matches!(ref_, Either::Right(ref r) if ***r == 456));
         */
        assert!(matches!(ref_, Either::Right(ref r) if *r.deref_target() == 456));

        /* Receive the reading permission.
         * Origin Rust: let ptr2 = <Either16 as NonNullPtr>::ref_as_raw(ref_);
         */
        proof_decl! { let ghost ref_value = ref_; }
        let (ptr2, ref_perm2) = <Either16 as NonNullPtr>::ref_as_raw(ref_);
        proof! {
            let addr = ptr.as_ptr().addr();
            let addr2 = ptr2.as_ptr().addr();
            assert(addr == addr2) by (bit_vector)
                requires
                    addr & 1usize == 1,
                    addr2 & 1usize == 1,
                    addr & !1usize == addr2 & !1usize,
            ;
        }
        assert_eq!(ptr, ptr2);

        /* Consume the ownership permission.
         * Origin Rust: let val = unsafe { <Either16 as NonNullPtr>::from_raw(ptr) };
         */
        let val = unsafe { <Either16 as NonNullPtr>::from_raw(ptr, perm) };
        assert!(matches!(val, Either::Right(ref r) if **r == 456));
        /* Unsupported explicit drop; use the same scope-exit drop.
         * Origin Rust: drop(val);
         */
    }

    /* #[ktest]
    fn rcu_store_load() {
        let rcu: RcuOption<Either32> = RcuOption::new_none();
        assert!(rcu.read().get().is_none());

        rcu.update(Some(Either::Left(Arc::new(888))));
        assert!(matches!(rcu.read().get().unwrap(), Either::Left(r) if **r == 888));

        rcu.update(Some(Either::Right(Box::new(999))));
        assert!(matches!(rcu.read().get().unwrap(), Either::Right(r) if **r == 999));
    } */
}
