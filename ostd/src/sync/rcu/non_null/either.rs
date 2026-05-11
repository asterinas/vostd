// SPDX-License-Identifier: MPL-2.0
use core::{marker::PhantomData, ptr::NonNull};

use vstd::raw_ptr::group_raw_ptr_axioms;
use vstd::{bits, prelude::*};
use vstd_extra::{external::nonzero::*, prelude::*, sum::Sum};

use super::{NonNullPtr, NonNullPtrRef};
use crate::util::Either;

verus! {

broadcast use {group_nonull_axioms, group_raw_ptr_axioms, group_nonzero_axioms};

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
    assert(addr & tag == 0) by (bit_vector)
        requires
            addr % (1usize << ptr_align_bits) == 0,
            tag == 1usize << align_bits,
            align_bits < ptr_align_bits < usize::BITS,
    ;
}

// If both `L` and `R` have at least one alignment bit (i.e., their alignments are at least 2), we
// can use the alignment bit to indicate whether a pointer is `L` or `R`, so it's possible to
// implement `NonNullPtr` for `Either<L, R>`.
unsafe impl<L: NonNullPtr, R: NonNullPtr> NonNullPtr for Either<L, R> {
    type Target = PhantomData<Self>;

    // type Ref<'a>
    //     = Either<L::Ref<'a>, R::Ref<'a>>
    // where
    //     Self: 'a;
    type Permission = Sum<L::Permission, R::Permission>;

    #[verifier::external_body]
    const ALIGN_BITS: u32 = min(L::ALIGN_BITS, R::ALIGN_BITS).checked_sub(1).expect(
        "`L` and `R` alignments should be at least 2 to pack `Either` into one pointer",
    );

    #[verus_spec]
    #[verifier::spinoff_prover]
    fn into_raw(self) -> (ret: (NonNull<Self::Target>, Tracked<Self::Permission>)) {
        proof_decl!{
           let ghost align_bits = Self::ALIGN_BITS;
           let ghost l_align_bits = L::ALIGN_BITS;
           let ghost r_align_bits = R::ALIGN_BITS;
           let ghost tag = 1usize << align_bits;
        }
        proof! {
            L::lemma_align_bits_range();
            R::lemma_align_bits_range();
            Self::lemma_align_bits_range();
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
                    let left_addr = left.cast::<Self::Target>().view_ptr_mut().addr();
                    let extra_bits: u32 = (l_align_bits - align_bits) as u32;
                    let scale = 1usize << extra_bits;
                    vstd::bits::lemma_usize_pow2_no_overflow(extra_bits as nat);
                    vstd::bits::lemma_usize_shl_is_mul(1, extra_bits as usize);
                    vstd::arithmetic::power2::lemma_pow2_adds(align_bits as nat, extra_bits as nat);
                    assert(left_addr % tag == 0) by {
                        let big = 1usize << l_align_bits;
                        let q = left_addr / big;
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(left_addr as int, big as int);
                        assert(left_addr as int == (q as int * scale as int) * tag as int) by (nonlinear_arith)
                        requires
                            left_addr as int == q as int * big as int,
                            big == tag * scale,
                        ;
                        vstd::arithmetic::div_mod::lemma_mod_multiples_basic(q as int * scale as int, tag as int);
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
                let right_tagged = right.map_addr_v(
                    |addr: NonZeroUsize| -> (ret: NonZeroUsize)
                        ensures
                            ret@ == addr@ | (1usize << Self::ALIGN_BITS),
                        { addr | 1usize << Self::ALIGN_BITS },
                );
                proof! {
                    let addr = right.addr_spec()@;
                    let tagged_addr = right_tagged.addr_spec()@;
                    assert(tagged_addr & tag == tag) by (bit_vector)
                    requires
                        tagged_addr == addr | tag,
                        tag == 1usize << align_bits,
                        1 <= r_align_bits < usize::BITS,
                        align_bits < r_align_bits,
                        addr % (1usize << r_align_bits) == 0,
                        addr != 0,
                    ;
                    let extra_bits: u32 = (r_align_bits - align_bits) as u32;
                    let scale = 1usize << extra_bits;
                    vstd::bits::lemma_usize_pow2_no_overflow(extra_bits as nat);
                    vstd::bits::lemma_usize_shl_is_mul(1, extra_bits as usize);
                    vstd::arithmetic::power2::lemma_pow2_adds(align_bits as nat, extra_bits as nat);
                    assert(tagged_addr == addr + tag) by (bit_vector)
                    requires
                        tagged_addr == addr | tag,
                        tag == 1usize << align_bits,
                        1 <= r_align_bits < usize::BITS,
                        align_bits < r_align_bits,
                        addr % (1usize << r_align_bits) == 0,
                        addr != 0,
                    ;
                    assert(addr % tag == 0) by {
                        let big = 1usize << r_align_bits;
                        let q = addr / big;
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(addr as int, big as int);
                        assert(addr as int == (q as int * scale as int) * tag as int) by (nonlinear_arith)
                        requires
                            addr as int == q as int * big as int,
                            big == tag * scale,
                        ;
                        vstd::arithmetic::div_mod::lemma_mod_multiples_basic(q as int * scale as int, tag as int);
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
            Self::lemma_align_bits_range();
        }
        proof_decl! {
            let ghost align_bits = Self::ALIGN_BITS;
            let ghost tag = 1usize << Self::ALIGN_BITS;
            let ghost ptr_addr = ptr.view_ptr_mut()@.addr;
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

    open spec fn ptr_perm_match(ptr: NonNull<Self::Target>, perm: Self::Permission) -> bool {
        let tag = 1usize << Self::ALIGN_BITS;
        match perm {
            Sum::Left(left) => {
                &&& ptr.view_ptr_mut().addr() & tag == 0
                &&& L::ptr_perm_match(ptr.cast(), left)
            },
            Sum::Right(right) => {
                let untagged_ptr = ptr.view_ptr_mut().with_addr((ptr.view_ptr_mut().addr() & !tag));
                let right_nonnull = nonnull_from_ptr_mut_spec(untagged_ptr);
                &&& ptr.view_ptr_mut().addr() & tag == tag
                &&& (ptr.view_ptr_mut().addr() & !tag) != 0
                &&& R::ptr_perm_match(right_nonnull.cast(), right)
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

    axiom fn lemma_align_bits_range()
        ensures
            Self::ALIGN_BITS == if L::ALIGN_BITS < R::ALIGN_BITS {
                L::ALIGN_BITS - 1
            } else {
                R::ALIGN_BITS - 1
            },
    ;
}

unsafe impl<'a, L: NonNullPtrRef<'a>, R: NonNullPtrRef<'a>> NonNullPtrRef<'a> for Either<L, R> {
    type Ref = Either<L::Ref, R::Ref>;

    type RefPermission = Sum<L::RefPermission, R::RefPermission>;

    open spec fn ref_perm_view_permission(perm: Self::RefPermission) -> Self::Permission {
        match perm {
            Sum::Left(left) => Sum::Left(L::ref_perm_view_permission(left)),
            Sum::Right(right) => Sum::Right(R::ref_perm_view_permission(right)),
        }
    }

    open spec fn ref_rel_perm(r: Self::Ref, perm: Self::RefPermission) -> bool {
        true
    }

    proof fn lemma_ref_perm_inv_impl_perm_inv(perm: Self::RefPermission) {
        match perm {
            Sum::Left(left) => L::lemma_ref_perm_inv_impl_perm_inv(left),
            Sum::Right(right) => R::lemma_ref_perm_inv_impl_perm_inv(right),
        }
    }

    unsafe fn raw_as_ref(
        raw: NonNull<Self::Target>,
        Tracked(perm): Tracked<Self::RefPermission>,
    ) -> Self::Ref {
        proof_decl! {
            let ghost align_bits = Self::ALIGN_BITS;
            let ghost tag = 1usize << align_bits;
            let ghost raw_addr = raw.view_ptr_mut()@.addr;
        }
        proof! {
            Self::lemma_align_bits_range();
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

    fn ref_as_raw(ptr_ref: Self::Ref) -> (NonNull<Self::Target>, Tracked<Self::RefPermission>) {
        proof!{
            Self::lemma_align_bits_range();
        }
        proof_decl!{
            let ghost align_bits = Self::ALIGN_BITS;
            let ghost tag = 1usize << align_bits;
            let ghost l_align_bits = L::ALIGN_BITS;
            let ghost r_align_bits = R::ALIGN_BITS;
        }
        proof!{
            L::lemma_align_bits_range();
            R::lemma_align_bits_range();
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
                    let ghost ptr_addr = ptr.view_ptr_mut().addr();
                    L::lemma_ref_perm_inv_impl_perm_inv(perm);
                    let extra_bits: u32 = (l_align_bits - align_bits) as u32;
                    let scale = 1usize << extra_bits;
                    vstd::bits::lemma_usize_pow2_no_overflow(extra_bits as nat);
                    vstd::bits::lemma_usize_shl_is_mul(1, extra_bits as usize);
                    vstd::arithmetic::power2::lemma_pow2_adds(align_bits as nat, extra_bits as nat);
                    assert(ptr_addr % tag == 0) by {
                        let big = 1usize << l_align_bits;
                        let q = ptr_addr / big;
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ptr_addr as int, big as int);
                        assert(ptr_addr as int == (q as int * scale as int) * tag as int) by (nonlinear_arith)
                        requires
                            ptr_addr as int == q as int * big as int,
                            big == tag * scale,
                        ;
                        vstd::arithmetic::div_mod::lemma_mod_multiples_basic(q as int * scale as int, tag as int);
                    };
                    assert(ptr_addr & tag == 0) by (bit_vector)
                    requires
                        ptr_addr % (1usize << l_align_bits) == 0,
                        tag == 1usize << align_bits,
                        align_bits < l_align_bits < usize::BITS,
                    ;
                }
                (ptr.cast(), Tracked(Sum::Left(perm)))
            },
            Either::Right(right) => {
                /* R::ref_as_raw(right)
                .map_addr(|addr| addr | (1 << Self::ALIGN_BITS))
                .cast() */
                let (ptr, Tracked(perm)) = R::ref_as_raw(right);
                proof! {
                    Self::lemma_align_bits_range();
                }
                let tagged_ptr = ptr.map_addr_v(
                    |addr: NonZeroUsize| -> (ret: NonZeroUsize)
                        ensures
                            ret@ == addr@ | (1usize << Self::ALIGN_BITS),
                        { addr | 1usize << Self::ALIGN_BITS },
                );
                proof! {
                    let ghost ptr_addr = ptr.view_ptr_mut().addr();
                    let ghost tagged_addr = tagged_ptr.view_ptr_mut().addr();
                    R::lemma_ref_perm_inv_impl_perm_inv(perm);
                    assert(tagged_addr & tag == tag) by (bit_vector)
                    requires
                        tagged_addr == ptr_addr | tag,
                        tag == 1usize << align_bits,
                        align_bits < r_align_bits < usize::BITS,
                        ptr_addr % (1usize << r_align_bits) == 0,
                        ptr_addr != 0,
                    ;
                    assert(ptr_addr & tag == 0) by (bit_vector)
                    requires
                        ptr_addr % (1usize << r_align_bits) == 0,
                        tag == 1usize << align_bits,
                        align_bits < r_align_bits < usize::BITS,
                    ;
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
                        assert(ptr_addr as int == (q as int * scale as int) * tag as int) by (nonlinear_arith)
                        requires
                            ptr_addr as int == q as int * big as int,
                            big == tag * scale,
                        ;
                        vstd::arithmetic::div_mod::lemma_mod_multiples_basic(q as int * scale as int, tag as int);
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

// A `min` implementation for use in constant evaluation.
#[vstd::contrib::auto_spec]
const fn min(a: u32, b: u32) -> u32 {
    if a < b {
        a
    } else {
        b
    }
}

/// # Safety
///
/// The caller must ensure that removing the bits from the non-null pointer will result in another
/// non-null pointer.
#[verus_spec(ret =>
    requires
        (ptr.view_ptr_mut().addr() & bits) < ptr.view_ptr_mut().addr(),
        (ptr.view_ptr_mut().addr() & !bits) != 0,
    ensures
        ret.0 == (ptr.view_ptr_mut().addr() & bits),
        ret.1.view_ptr_mut() == ptr.view_ptr_mut().with_addr((ptr.view_ptr_mut().addr() & !bits) as usize),
)]
unsafe fn remove_bits<T>(ptr: NonNull<T>, bits: usize) -> (usize, NonNull<T>) {
    // use core::num::NonZeroUsize;
    use vstd_extra::external::nonzero::NonZeroUsize;

    let removed_bits = ptr.addr_v().get() & bits;
    let result_ptr = ptr.map_addr_v(
        |addr| -> (ret: NonZeroUsize)
            ensures
                ret@ == addr@ & !bits,
            {
                // SAFETY: The safety is upheld by the caller.
                unsafe { NonZeroUsize::new_unchecked(addr.get() & !bits) }
            },
    );
    (removed_bits, result_ptr)
}

} // verus!
#[cfg(ktest)]
mod test {
    use alloc::{boxed::Box, sync::Arc};

    use super::*;
    use crate::{prelude::ktest, sync::RcuOption};

    type Either32 = Either<Arc<u32>, Box<u32>>;
    type Either16 = Either<Arc<u32>, Box<u16>>;

    #[ktest]
    fn alignment() {
        assert_eq!(<Either32 as NonNullPtr>::ALIGN_BITS, 1);
        assert_eq!(<Either16 as NonNullPtr>::ALIGN_BITS, 0);
    }

    #[ktest]
    fn left_pointer() {
        let val: Either16 = Either::Left(Arc::new(123));

        let ptr = NonNullPtr::into_raw(val);
        assert_eq!(ptr.addr().get() & 1, 0);

        let ref_ = unsafe { <Either16 as NonNullPtr>::raw_as_ref(ptr) };
        assert!(matches!(ref_, Either::Left(ref r) if ***r == 123));

        let ptr2 = <Either16 as NonNullPtr>::ref_as_raw(ref_);
        assert_eq!(ptr, ptr2);

        let val = unsafe { <Either16 as NonNullPtr>::from_raw(ptr) };
        assert!(matches!(val, Either::Left(ref r) if **r == 123));
        drop(val);
    }

    #[ktest]
    fn right_pointer() {
        let val: Either16 = Either::Right(Box::new(456));

        let ptr = NonNullPtr::into_raw(val);
        assert_eq!(ptr.addr().get() & 1, 1);

        let ref_ = unsafe { <Either16 as NonNullPtr>::raw_as_ref(ptr) };
        assert!(matches!(ref_, Either::Right(ref r) if ***r == 456));

        let ptr2 = <Either16 as NonNullPtr>::ref_as_raw(ref_);
        assert_eq!(ptr, ptr2);

        let val = unsafe { <Either16 as NonNullPtr>::from_raw(ptr) };
        assert!(matches!(val, Either::Right(ref r) if **r == 456));
        drop(val);
    }

    #[ktest]
    fn rcu_store_load() {
        let rcu: RcuOption<Either32> = RcuOption::new_none();
        assert!(rcu.read().get().is_none());

        rcu.update(Some(Either::Left(Arc::new(888))));
        assert!(matches!(rcu.read().get().unwrap(), Either::Left(r) if **r == 888));

        rcu.update(Some(Either::Right(Box::new(999))));
        assert!(matches!(rcu.read().get().unwrap(), Either::Right(r) if **r == 999));
    }
}
