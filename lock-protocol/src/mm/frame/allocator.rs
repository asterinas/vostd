use vstd::prelude::*;

use std::sync::{Mutex, OnceLock};

use vstd::vpanic;
use vstd::rwlock::RwLock;
use vstd::simple_pptr::{PPtr, PointsTo};

use crate::exec::{MockPageTablePage, MockPageTableEntry, PHYSICAL_BASE_ADDRESS_SPEC, SIZEOF_FRAME};

use super::meta::AnyFrameMeta;
use super::Frame;

verus! {

/// We assume that the available physical memory is 0 to MAX_FRAME_NUM - 1.
pub const MAX_FRAME_NUM: usize = 10000;

pub open spec fn pa_is_valid_kernel_address(pa: int) -> bool {
    PHYSICAL_BASE_ADDRESS_SPEC() <= pa < PHYSICAL_BASE_ADDRESS_SPEC() + SIZEOF_FRAME
        * MAX_FRAME_NUM as int
}

/// Each user of the global allocator can instantiate such a model for reasoning.
///
/// So that the user can know that, each new allocation must be a new address,
/// different from any previous allocations.
pub tracked struct AllocatorModel<M: AnyFrameMeta> {
    /// Maps from the allocated frame address to the metadata.
    pub meta_map: Map<int, PointsTo<M>>,
}

impl<M: AnyFrameMeta> AllocatorModel<M> {
    pub open spec fn invariants(&self) -> bool {
        forall|addr: int| #[trigger]
            self.meta_map.contains_key(addr) ==> {
                &&& pa_is_valid_kernel_address(addr)
                &&& addr % SIZEOF_FRAME as int == 0
                &&& self.meta_map[addr].mem_contents().is_init()
            }
    }
}

#[verifier::external_body]
pub fn alloc<F, R>(mut alloc_fn: F) -> R where F: FnMut(&mut MockGlobalAllocator) -> R {
    static GLOBAL_ALLOCATOR: OnceLock<Mutex<MockGlobalAllocator>> = OnceLock::new();

    let allocator_lock = GLOBAL_ALLOCATOR.get_or_init(|| Mutex::new(MockGlobalAllocator::init()));
    let mut allocator = allocator_lock.lock().unwrap();

    alloc_fn(&mut allocator)
}

pub struct MockGlobalAllocator {
    pub frames: [Option<
        (PPtr<MockPageTablePage>, Tracked<PointsTo<MockPageTablePage>>),
    >; MAX_FRAME_NUM],
}

impl MockGlobalAllocator {
    pub open spec fn has_available_frames(&self) -> bool {
        exists|i: usize| 0 <= i < MAX_FRAME_NUM && self.frames[i as int].is_some()
    }

    pub open spec fn invariants<M: AnyFrameMeta>(&self, model: &AllocatorModel<M>) -> bool {
        &&& forall|i: usize|
            0 <= i < MAX_FRAME_NUM ==> {
                #[trigger] model.meta_map.contains_key(
                    (PHYSICAL_BASE_ADDRESS_SPEC() + i * SIZEOF_FRAME) as int,
                ) ==> self.frames[i as int].is_some()
            }
        &&& forall|i: usize|
            0 <= i < MAX_FRAME_NUM ==> {
                if let Some((p, _)) = #[trigger] self.frames[i as int] {
                    p.addr() == (PHYSICAL_BASE_ADDRESS_SPEC() + i * SIZEOF_FRAME) as int
                } else {
                    true
                }
            }
    }

    #[verifier::external_body]
    pub fn init() -> (res: MockGlobalAllocator)
        ensures
            res.has_available_frames(),
    {
        let mut frames = [const { None };MAX_FRAME_NUM];

        for i in 0..MAX_FRAME_NUM {
            let pptr = PPtr::<MockPageTablePage>::from_addr(i * SIZEOF_FRAME);
            frames[i] = Some((pptr, Tracked::assume_new()));
        }

        MockGlobalAllocator { frames }
    }

    #[verifier::external_body]
    pub fn alloc<M: AnyFrameMeta>(
        &mut self,
        meta: M,
        Tracked(model): Tracked<&mut AllocatorModel<M>>,
    ) -> (res: (Frame<M>, Tracked<PointsTo<MockPageTablePage>>))
        requires
            old(self).invariants(old(model)),
            old(self).has_available_frames(),
            old(model).invariants(),
        ensures
            self.invariants(model),
            model.invariants(),
            !old(model).meta_map.contains_key(res.0.start_paddr() as int),
            model.meta_map.contains_key(res.0.start_paddr() as int),
            model.meta_map[res.0.start_paddr() as int].value() == meta,
            res.1@.pptr() == res.0.ptr,
            res.0.start_paddr() < PHYSICAL_BASE_ADDRESS_SPEC() + SIZEOF_FRAME * MAX_FRAME_NUM,
            forall|i: usize|
                0 <= i < MAX_FRAME_NUM ==> {
                    if #[trigger] self.frames[i as int].is_some() {
                        self.frames[i as int].unwrap().1@.pptr() == self.frames[i as int].unwrap().0
                    } else {
                        true
                    }
                },
    {
        for i in 0..MAX_FRAME_NUM {
            if !self.frames[i].is_none() {
                let (ptr, pt_perm) = self.frames[i].take().unwrap();

                let (meta_ptr, Tracked(meta_perm)) = PPtr::new(meta);

                proof {
                    model.meta_map.insert(ptr.addr() as int, meta_perm);
                }

                return (Frame { meta_ptr, ptr }, pt_perm);
            }
        }
        vpanic!("No available frames");
    }
}

} // verus!
