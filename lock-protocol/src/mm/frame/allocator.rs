use vstd::prelude::*;

use std::sync::{Mutex, OnceLock};

use vstd::vpanic;
use vstd::rwlock::RwLock;
use vstd::simple_pptr::{PPtr, PointsTo};

use crate::exec::{MockPageTablePage, MockPageTableEntry, PHYSICAL_BASE_ADDRESS_SPEC, SIZEOF_FRAME};

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
pub tracked struct AllocatorModel {
    pub ghost allocated_addrs: Set<int>,
}

impl AllocatorModel {
    pub open spec fn invariants(&self) -> bool {
        forall|addr: int| #[trigger]
            self.allocated_addrs.contains(addr) ==> {
                &&& pa_is_valid_kernel_address(addr)
                &&& addr % SIZEOF_FRAME as int == 0
            }
    }
}

#[verifier::external_body]
pub fn alloc_page_table(Tracked(model): Tracked<&mut AllocatorModel>) -> (res: (
    PPtr<MockPageTablePage>,
    Tracked<PointsTo<MockPageTablePage>>,
))
    requires
        old(model).invariants(),
    ensures
        res.1@.pptr() == res.0,
        res.1@.mem_contents().is_init(),
        pa_is_valid_kernel_address(res.0.addr() as int),
        model.invariants(),
        !old(model).allocated_addrs.contains(res.0.addr() as int),
        model.allocated_addrs.contains(res.0.addr() as int),
{
    static GLOBAL_ALLOCATOR: OnceLock<Mutex<MockGlobalAllocator>> = OnceLock::new();

    let allocator_lock = GLOBAL_ALLOCATOR.get_or_init(|| Mutex::new(MockGlobalAllocator::init()));
    let mut allocator = allocator_lock.lock().unwrap();

    allocator.alloc()
}

pub struct MockGlobalAllocator {
    pub frames: [Option<
        (PPtr<MockPageTablePage>, Tracked<PointsTo<MockPageTablePage>>),
    >; MAX_FRAME_NUM],
}

impl MockGlobalAllocator {
    pub closed spec fn invariants(&self) -> bool {
        forall|i: usize|
            0 <= i < MAX_FRAME_NUM ==> {
                if let Some((p, _)) = #[trigger] self.frames[i as int] {
                    p.addr() == PHYSICAL_BASE_ADDRESS_SPEC() + i * SIZEOF_FRAME
                } else {
                    true
                }
            }
    }

    #[verifier::external_body]
    pub fn init() -> MockGlobalAllocator {
        let mut frames = [const { None };MAX_FRAME_NUM];

        for i in 0..MAX_FRAME_NUM {
            let pptr = PPtr::<MockPageTablePage>::from_addr(i * SIZEOF_FRAME);
            frames[i] = Some((pptr, Tracked::assume_new()));
        }

        MockGlobalAllocator { frames }
    }

    #[verifier::external_body]
    pub fn alloc(&mut self) -> (res: (
        PPtr<MockPageTablePage>,
        Tracked<PointsTo<MockPageTablePage>>,
    ))
        requires
            exists|i: usize| 0 <= i < MAX_FRAME_NUM && old(self).frames[i as int].is_some(),
        ensures
            res.1@.pptr() == res.0,
            res.0.addr() < PHYSICAL_BASE_ADDRESS_SPEC() + SIZEOF_FRAME * MAX_FRAME_NUM,
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
                let (p, pt) = self.frames[i].take().unwrap();
                return (p, pt);
            }
        }
        vpanic!("No available frames");
    }
}

} // verus!
