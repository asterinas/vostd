// SPDX-License-Identifier: MPL-2.0
use core::{marker::PhantomData, ptr::NonNull};

use vstd::prelude::*;
use vstd_extra::{prelude::*, sum::Sum};

use super::NonNullPtr;
use crate::util::Either;

verus! {

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
            Sum::Left(left) => left.ptr() as *mut Self::Target,
            Sum::Right(right) => (right.ptr() as *mut Self::Target).with_addr(
                right.ptr().addr() | (1usize << <Either<L::Ptr, R::Ptr> as NonNullPtr>::ALIGN_BITS),
            ),
        }
    }

    open spec fn addr(self) -> usize {
        self.ptr().addr()
    }

    open spec fn view_target(self) -> Self::Target {
        PhantomData
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

    fn into_raw(self) -> (ret: (NonNull<Self::Target>, Tracked<Self::Permission>)) {
        /* match self {
            Self::Left(left) => left.into_raw().cast(),
            Self::Right(right) => right
                .into_raw()
                .map_addr(|addr| addr | (1 << Self::ALIGN_BITS))
                .cast(),
        } */
        match self {
            Self::Left(left) => {
                let (ptr, Tracked(perm)) = left.into_raw();
                let raw = ptr.as_ptr().cast::<Self::Target>();
                proof! {
                    L::lemma_ptr_perm_addr(ptr, perm);
                    assume(Self::ALIGN_BITS < usize::BITS);
                    assume(Self::ALIGN_BITS < L::ALIGN_BITS);
                    L::lemma_ptr_perm_low_bit_zero(ptr, perm, Self::ALIGN_BITS);
                    let tag = 1usize << Self::ALIGN_BITS;
                    assert(raw@.addr == ptr.view_ptr_mut().addr());
                    assert(raw@.addr == perm.ptr().addr());
                    assert(raw@.addr & tag == 0);
                    assert(raw@.addr != 0);
                    let raw_addr = raw@.addr;
                    let either_perm: EitherPointsTo<L::Permission, R::Permission> =
                        EitherPointsTo { perm: Sum::Left(perm) };
                    assert(either_perm.ptr().addr() == perm.ptr().addr());
                    assert(raw@.addr == either_perm.ptr().addr());
                    assert((raw_addr & !tag) != 0) by (bit_vector)
                        requires
                            raw_addr != 0,
                            (raw_addr & tag) == 0,
                    ;
                }
                (unsafe { NonNull::new_unchecked(raw) }, Tracked(EitherPointsTo { perm: Sum::Left(perm) }))
            },
            Self::Right(right) => {
                let (ptr, Tracked(perm)) = right.into_raw();
                let raw = ptr.as_ptr().cast::<Self::Target>();
                proof! {
                    R::lemma_ptr_perm_addr(ptr, perm);
                    assume(Self::ALIGN_BITS < usize::BITS);
                    assume(Self::ALIGN_BITS < R::ALIGN_BITS);
                    R::lemma_ptr_perm_low_bit_zero(ptr, perm, Self::ALIGN_BITS);
                    assert(raw@.addr != 0);
                }
                let tag = 1usize << Self::ALIGN_BITS;
                let tagged_raw = raw.with_addr(raw.addr() | tag);
                proof! {
                    let addr = raw@.addr;
                    assert(tagged_raw@.addr == (raw@.addr | tag));
                    assert((addr | tag) != 0) by (bit_vector)
                        requires
                            addr != 0,
                    ;
                    assert(tagged_raw@.addr != 0);
                }
                let ret_ptr = unsafe { NonNull::new_unchecked(tagged_raw) };
                proof! {
                    let tag = 1usize << Self::ALIGN_BITS;
                    let either_perm = EitherPointsTo { perm: Sum::Right(perm) };
                    let addr = ret_ptr.view_ptr_mut().addr();
                    let raw_addr = raw@.addr;
                    assert(ret_ptr.view_ptr_mut().addr() == tagged_raw@.addr);
                    assert(ret_ptr.view_ptr_mut().addr() == (raw_addr | tag));
                    assert((raw_addr & tag) == 0);
                    assert((addr & !tag) != 0) by (bit_vector)
                        requires
                            addr == (raw_addr | tag),
                            (raw_addr & tag) == 0,
                            raw_addr != 0,
                    ;
                    assert((addr & tag) == tag) by (bit_vector)
                        requires
                            addr == (raw_addr | tag),
                            (raw_addr & tag) == 0,
                    ;
                    assert(either_perm.ptr().addr() == (perm.ptr().addr() | tag));
                    assert(perm.ptr().addr() == raw_addr);
                    assert(either_perm.ptr().addr() == ret_ptr.view_ptr_mut().addr());
                    assert(Self::ptr_perm_match(ret_ptr, either_perm));
                }
                (
                    ret_ptr,
                    Tracked(EitherPointsTo { perm: Sum::Right(perm) }),
                )
            },
        }
    }

    unsafe fn from_raw(
        ptr: NonNull<Self::Target>,
        perm_exec: Tracked<Self::Permission>,
    ) -> Self {
        proof! {
            assume(Self::ALIGN_BITS < usize::BITS);
        }
        // SAFETY: The caller ensures that the pointer comes from `Self::into_raw`, which
        // guarantees that `real_ptr` is a non-null pointer.
        let bits = 1 << Self::ALIGN_BITS;
        proof_decl! {
            let tracked perm = perm_exec.get();
        }
        proof! {
            let addr = ptr.view_ptr_mut().addr();
            assert(Self::ptr_perm_match(ptr, perm));
            match perm.perm {
                Sum::Left(_) => {
                    assert(perm.ptr().addr() == addr);
                    assert((addr & bits) == 0);
                    assert((addr & !bits) != 0);
                    assert((addr & bits) < addr) by (bit_vector)
                        requires
                            (addr & bits) == 0,
                            (addr & !bits) != 0,
                    ;
                },
                Sum::Right(_) => {
                    assert(perm.ptr().addr() == addr);
                    assert((addr & bits) == bits);
                    assert((addr & !bits) != 0);
                    assert((addr & bits) < addr) by (bit_vector)
                        requires
                            (addr & bits) == bits,
                            (addr & !bits) != 0,
                    ;
                },
            }
        }
        let (_is_right, real_ptr) = unsafe { remove_bits(ptr, bits) };

        /* if is_right == 0 {
            // SAFETY: `Self::into_raw` guarantees that `real_ptr` comes from `L::into_raw`. Other
            // safety requirements are upheld by the caller.
            Either::Left(unsafe { L::from_raw(real_ptr.cast()) })
        } else {
            // SAFETY: `Self::into_raw` guarantees that `real_ptr` comes from `R::into_raw`. Other
            // safety requirements are upheld by the caller.
            Either::Right(unsafe { R::from_raw(real_ptr.cast()) })
        } */

        if _is_right == 0 {
            proof_decl! {
                let tracked left = match perm.perm {
                    Sum::Left(left) => left,
                    Sum::Right(right) => {
                        assert(Self::ptr_perm_match(ptr, perm));
                        assert(ptr.view_ptr_mut().addr() & bits == _is_right);
                        assert(ptr.view_ptr_mut().addr() & bits == 0);
                        assert((ptr.view_ptr_mut().addr() & bits) == bits);
                        assume(bits != 0);
                        assert(false);
                        proof_from_false()
                    },
                };
            }
            proof! {
                let addr = ptr.view_ptr_mut().addr();
                assert(real_ptr.view_ptr_mut().addr() == (addr & !bits));
                assert(real_ptr.cast::<L::Target>().view_ptr_mut().addr() == real_ptr.view_ptr_mut().addr());
                assert(addr == left.ptr().addr());
                assert((addr & bits) == 0);
                assert((addr & !bits) == addr) by (bit_vector)
                    requires
                        (addr & bits) == 0,
                ;
                assert(real_ptr.cast::<L::Target>().view_ptr_mut().addr() == left.ptr().addr());
                L::lemma_ptr_perm_from_addr(real_ptr.cast(), left);
            }
            Either::Left(unsafe { L::from_raw(real_ptr.cast(), Tracked(left)) })
        } else {
            proof_decl! {
                let tracked right = match perm.perm {
                    Sum::Right(right) => right,
                    Sum::Left(left) => {
                        assert(Self::ptr_perm_match(ptr, perm));
                        assert(ptr.view_ptr_mut().addr() & bits == _is_right);
                        assert(ptr.view_ptr_mut().addr() & bits != 0);
                        assert(ptr.view_ptr_mut().addr() == left.ptr().addr());
                        assert((ptr.view_ptr_mut().addr() & bits) == 0);
                        assert(false);
                        proof_from_false()
                    },
                };
            }
            proof! {
                let addr = ptr.view_ptr_mut().addr();
                let raw_addr = right.ptr().addr();
                assert(real_ptr.view_ptr_mut().addr() == (addr & !bits));
                assert(real_ptr.cast::<R::Target>().view_ptr_mut().addr() == real_ptr.view_ptr_mut().addr());
                assert(addr == (raw_addr | bits));
                assert((addr & !bits) == raw_addr) by (bit_vector)
                    requires
                        addr == (raw_addr | bits),
                        (raw_addr & bits) == 0,
                ;
                assert(real_ptr.cast::<R::Target>().view_ptr_mut().addr() == right.ptr().addr());
                R::lemma_ptr_perm_from_addr(real_ptr.cast(), right);
            }
            Either::Right(unsafe { R::from_raw(real_ptr.cast(), Tracked(right)) })
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
        let tag = 1usize << Self::ALIGN_BITS;
        match perm.perm {
            Sum::Left(left) => perm.ptr().addr() == ptr.view_ptr_mut().addr()
                && (ptr.view_ptr_mut().addr() & tag) == 0
                && (ptr.view_ptr_mut().addr() & !tag) != 0,
            Sum::Right(right) => perm.ptr().addr() == ptr.view_ptr_mut().addr()
                && (ptr.view_ptr_mut().addr() & tag) == tag
                && (ptr.view_ptr_mut().addr() & !tag) != 0,
        }
    }

    proof fn lemma_ptr_perm_addr(ptr: NonNull<Self::Target>, perm: Self::Permission)
    {
        assert(ptr.view_ptr_mut().addr() == perm.ptr().addr());
    }

    proof fn lemma_ptr_perm_low_bit_zero(
        ptr: NonNull<Self::Target>,
        perm: Self::Permission,
        bit: u32,
    )
    {
        match perm.perm {
            Sum::Left(left) => {
                assert(ptr.view_ptr_mut().addr() == left.ptr().addr());
                assume(Self::ALIGN_BITS < L::ALIGN_BITS);
                assume(left.ptr().addr() & (1usize << bit) == 0);
                assume(ptr.view_ptr_mut().addr() & (1usize << bit) == 0);
            },
            Sum::Right(right) => {
                assume(Self::ALIGN_BITS < R::ALIGN_BITS);
                assume(right.ptr().addr() & (1usize << bit) == 0);
                assume(ptr.view_ptr_mut().addr() & (1usize << bit) == 0);
            },
        }
    }

    proof fn lemma_ptr_perm_from_addr(ptr: NonNull<Self::Target>, perm: Self::Permission)
    {
        let tag = 1usize << Self::ALIGN_BITS;
        let addr = ptr.view_ptr_mut().addr();
        match perm.perm {
            Sum::Left(left) => {
                assert(perm.ptr().addr() == left.ptr().addr());
                assert(addr == left.ptr().addr());
                ptr.lemma_addr_is_nonnull();
                assume(Self::ALIGN_BITS < usize::BITS);
                assume(Self::ALIGN_BITS < L::ALIGN_BITS);
                let left_ptr: NonNull<L::Target> =
                    vstd_extra::external::nonnull::nonnull_from_ptr_mut_spec(left.ptr());
                assert(left_ptr.view_ptr_mut() == left.ptr());
                L::lemma_ptr_perm_from_addr(left_ptr, left);
                L::lemma_ptr_perm_low_bit_zero(left_ptr, left, Self::ALIGN_BITS);
                assert((left.ptr().addr() & tag) == 0);
                assert((left.ptr().addr() & !tag) != 0) by (bit_vector)
                    requires
                        left.ptr().addr() != 0,
                        (left.ptr().addr() & tag) == 0,
                ;
                assert((addr & tag) == 0);
                assert((addr & !tag) != 0);
                assert(Self::ptr_perm_match(ptr, EitherPointsTo { perm: Sum::Left(left) }));
            },
            Sum::Right(right) => {
                let raw_addr = right.ptr().addr();
                assert(perm.ptr().addr() == (raw_addr | tag));
                assert(addr == (raw_addr | tag));
                assume(Self::ALIGN_BITS < usize::BITS);
                assume(Self::ALIGN_BITS < R::ALIGN_BITS);
                assume((raw_addr & tag) == 0);
                assume(raw_addr != 0);
                assert((addr & tag) == tag) by (bit_vector)
                    requires
                        addr == (raw_addr | tag),
                        (raw_addr & tag) == 0,
                ;
                assert((addr & !tag) != 0) by (bit_vector)
                    requires
                        addr == (raw_addr | tag),
                        (raw_addr & tag) == 0,
                        raw_addr != 0,
                ;
                assert(Self::ptr_perm_match(ptr, EitherPointsTo { perm: Sum::Right(right) }));
            },
        }
    }

    open spec fn rel_perm(self, perm: Self::Permission) -> bool {
        match (self, perm.perm) {
            (Either::Left(left), Sum::Left(left_perm)) => left.rel_perm(left_perm),
            (Either::Right(right), Sum::Right(right_perm)) => right.rel_perm(right_perm),
            _ => false,
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
#[verus_spec(
    requires
        (ptr.view_ptr_mut()@.addr & bits) < ptr.view_ptr_mut()@.addr,
        (ptr.view_ptr_mut()@.addr & !bits) != 0,
)]
unsafe fn remove_bits<T>(ptr: NonNull<T>, bits: usize) -> (ret: (usize, NonNull<T>))
    ensures
        ret.0 == (ptr.view_ptr_mut()@.addr & bits),
        ret.1.view_ptr_mut()@.addr == (ptr.view_ptr_mut()@.addr & !bits),
{
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
