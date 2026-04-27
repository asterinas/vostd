// SPDX-License-Identifier: MPL-2.0
use core::{marker::PhantomData, ptr::NonNull};

use vstd::{bits, prelude::*};
use vstd::raw_ptr::group_raw_ptr_axioms;
use vstd_extra::{prelude::*, sum::Sum};

use super::NonNullPtr;
use crate::util::Either;

verus! {

broadcast use {group_nonull_axioms, group_raw_ptr_axioms};

pub tracked struct EitherPointsTo<L: PtrPointsToTrait, R: PtrPointsToTrait> {
    pub perm: Sum<L, R>,
}

impl<L: PtrPointsToTrait, R: PtrPointsToTrait> PtrPointsToTrait for EitherPointsTo<L, R>
    where
        L::Ptr: NonNullPtr,
        R::Ptr: NonNullPtr,
{
    type Ptr = Either<L::Ptr, R::Ptr>;

    type Target = PhantomData<Self::Ptr>;

    open spec fn ptr(self) -> *mut Self::Target {
        match self.perm {
            Sum::Left(left) => left.ptr().cast(),
            Sum::Right(right) => right.ptr().cast(),
        }
    }

    open spec fn view_target(self) -> Self::Target {
        PhantomData
    }
}

impl<L: PtrPointsToTrait, R: PtrPointsToTrait> EitherPointsTo<L, R>
where
    L::Ptr: NonNullPtr,
    R::Ptr: NonNullPtr,
{
    pub open spec fn addr(self) -> usize {
        self.ptr().addr()
    }
}

impl<L: PtrPointsToTrait + Inv, R: PtrPointsToTrait + Inv> Inv for EitherPointsTo<L, R> {
    closed spec fn inv(self) -> bool {
        match self.perm {
            Sum::Left(left) => left.inv(),
            Sum::Right(right) => right.inv(),
        }
    }
}

// If both `L` and `R` have at least one alignment bit (i.e., their alignments are at least 2), we
// can use the alignment bit to indicate whether a pointer is `L` or `R`, so it's possible to
// implement `NonNullPtr` for `Either<L, R>`.
unsafe impl<L: NonNullPtr, R: NonNullPtr> NonNullPtr for Either<L, R> {
    type Target = PhantomData<Self>;

    type Permission = EitherPointsTo<L::Permission, R::Permission>;

    // type Ref<'a>
    //     = Either<L::Ref<'a>, R::Ref<'a>>
    // where
    //     Self: 'a;
    #[verifier::external_body]
    const ALIGN_BITS: u32 = min(L::ALIGN_BITS, R::ALIGN_BITS)
        .checked_sub(1)
        .expect("`L` and `R` alignments should be at least 2 to pack `Either` into one pointer");

    #[verus_spec]
    fn into_raw(self) -> (ret: (NonNull<Self::Target>, Tracked<Self::Permission>)) {
        /* match self {
            Self::Left(left) => left.into_raw().cast(),
            Self::Right(right) => right
                .into_raw()
                .map_addr(|addr| addr | (1 << Self::ALIGN_BITS))
                .cast(),
        } */
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
            assume(Self::ALIGN_BITS == min(L::ALIGN_BITS, R::ALIGN_BITS) - 1);
            vstd::bits::lemma_usize_pow2_no_overflow(align_bits as nat);
            vstd::bits::lemma_usize_pow2_no_overflow(l_align_bits as nat);
            vstd::bits::lemma_usize_pow2_no_overflow(r_align_bits as nat);
            vstd::bits::lemma_usize_shl_is_mul(1, align_bits as usize);
            vstd::bits::lemma_usize_shl_is_mul(1, l_align_bits as usize);
            vstd::bits::lemma_usize_shl_is_mul(1, r_align_bits as usize);
        }
        match self {
            Self::Left(left) => {
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
                        assert(big != 0) by (nonlinear_arith)
                        requires
                            big == tag * scale,
                            tag > 0,
                            scale > 0,
                        ;
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(left_addr as int, big as int);
                        assert(left_addr as int == (q as int * scale as int) * tag as int) by (nonlinear_arith)
                        requires
                            left_addr as int == q as int * big as int,
                            big == tag * scale,
                        ;
                        vstd::arithmetic::div_mod::lemma_mod_multiples_basic(q as int * scale as int, tag as int);
                    };
                }
                (left.cast() , Tracked(EitherPointsTo { perm: Sum::Left(perm) }))
            },
            Self::Right(right) => {
                let (right, Tracked(perm)) = right.into_raw();
                let right_raw = right.as_ptr().map_addr(|addr| -> (ret: usize) 
                    ensures ret == addr | (1usize << Self::ALIGN_BITS)
                    {addr | (1usize << Self::ALIGN_BITS)});
                proof! {
                    let addr = right.as_ptr().addr();
                    let tagged_addr = right_raw.addr();
                    assert(tagged_addr & !tag == addr) by (bit_vector)
                    requires
                        tagged_addr == addr | tag,
                        tag == 1usize << align_bits,
                        1 <= r_align_bits < usize::BITS,
                        align_bits < r_align_bits,
                        addr % (1usize << r_align_bits) == 0,
                        addr != 0,
                    ;
                    assert(tagged_addr != 0) by (bit_vector)
                    requires
                        tagged_addr == addr | tag,
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
                    assert(tagged_addr % (1usize << align_bits) == 0) by {
                        vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(addr as int, tag as int);
                    }
                }
                (
                    unsafe { NonNull::new_unchecked(right_raw) }.cast(),
                    Tracked(EitherPointsTo { perm: Sum::Right(perm) }),
                )
            },
        }
    }

    #[verifier::external_body]
    unsafe fn from_raw(
        ptr: NonNull<Self::Target>,
        perm_exec: Tracked<Self::Permission>,
    ) -> Self {
        // SAFETY: The caller ensures that the pointer comes from `Self::into_raw`, which
        // guarantees that `real_ptr` is a non-null pointer.
        let (_is_right, real_ptr) = unsafe { remove_bits(ptr, 1 << Self::ALIGN_BITS) };

        /* if is_right == 0 {
            // SAFETY: `Self::into_raw` guarantees that `real_ptr` comes from `L::into_raw`. Other
            // safety requirements are upheld by the caller.
            Either::Left(unsafe { L::from_raw(real_ptr.cast()) })
        } else {
            // SAFETY: `Self::into_raw` guarantees that `real_ptr` comes from `R::into_raw`. Other
            // safety requirements are upheld by the caller.
            Either::Right(unsafe { R::from_raw(real_ptr.cast()) })
        } */

        match perm_exec.get().perm {
            Sum::Left(left) => Either::Left(unsafe { L::from_raw(real_ptr.cast(), Tracked(left)) }),
            Sum::Right(right) => {
                Either::Right(unsafe { R::from_raw(real_ptr.cast(), Tracked(right)) })
            },
        }
    }

    /* unsafe fn raw_as_ref<'a>(raw: NonNull<Self::Target>) -> Self::Ref<'a> {
        // SAFETY: The caller ensures that the pointer comes from `Self::into_raw`, which
        // guarantees that `real_ptr` is a non-null pointer.
        let (is_right, real_ptr) = unsafe { remove_bits(raw, 1 << Self::ALIGN_BITS) };

        if is_right == 0 {
            // SAFETY: `Self::into_raw` guarantees that `real_ptr` comes from `L::into_raw`. Other
            // safety requirements are upheld by the caller.
            Either::Left(unsafe { L::raw_as_ref(real_ptr.cast()) })
        } else {
            // SAFETY: `Self::into_raw` guarantees that `real_ptr` comes from `R::into_raw`. Other
            // safety requirements are upheld by the caller.
            Either::Right(unsafe { R::raw_as_ref(real_ptr.cast()) })
        }
    } */

    /* fn ref_as_raw(ptr_ref: Self::Ref<'_>) -> NonNull<Self::Target> {
        match ptr_ref {
            Either::Left(left) => L::ref_as_raw(left).cast(),
            Either::Right(right) => R::ref_as_raw(right)
                .map_addr(|addr| addr | (1 << Self::ALIGN_BITS))
                .cast(),
        }
    } */

    open spec fn ptr_perm_match(ptr: NonNull<Self::Target>, perm: Self::Permission) -> bool {
        match perm.perm {
            Sum::Left(left) => L::ptr_perm_match(ptr.cast(), left),
            Sum::Right(right) => {
                let tag = 1usize << Self::ALIGN_BITS;
                let untagged_ptr = ptr.view_ptr_mut().with_addr(ptr.view_ptr_mut().addr() & !tag);
                let right_nonnull = nonnull_from_ptr_mut_spec(untagged_ptr);
                R::ptr_perm_match(right_nonnull.cast(), right)
            }
        }
    }

    open spec fn rel_perm(self, perm: Self::Permission) -> bool {
        match (self, perm.perm) {
            (Either::Left(left), Sum::Left(left_perm)) => left.rel_perm(left_perm),
            (Either::Right(right), Sum::Right(right_perm)) => right.rel_perm(right_perm),
            _ => false,
        }
    }

    axiom fn lemma_align_bits_range(); 
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
#[verus_spec(
    requires
        (ptr.view_ptr_mut()@.addr & bits) < ptr.view_ptr_mut()@.addr,
        (ptr.view_ptr_mut()@.addr & !bits) != 0,
)]
unsafe fn remove_bits<T>(ptr: NonNull<T>, bits: usize) -> (usize, NonNull<T>) {
    // use core::num::NonZeroUsize;
    // let removed_bits = ptr.addr().get() & bits;
    let raw = ptr.as_ptr();
    let Tracked(exposed) = vstd::raw_ptr::expose_provenance(raw);
    let addr = raw as usize;
    let removed_bits = addr & bits;
    // let result_ptr = ptr.map_addr(|addr|
    //     // SAFETY: The safety is upheld by the caller.
    //     unsafe { NonZeroUsize::new_unchecked(addr.get() & !bits) });
    let result_raw = vstd::raw_ptr::with_exposed_provenance(addr & !bits, Tracked(exposed));
    let result_ptr = unsafe { NonNull::new_unchecked(result_raw) };

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
