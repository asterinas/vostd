use vstd::prelude::*;

use std::sync::{Mutex, OnceLock};

use vstd::vpanic;
use vstd::rwlock::RwLock;
use vstd::simple_pptr::{PPtr, PointsTo};

use crate::mm::PAGE_SIZE;
use crate::exec::{MockPageTablePage, MockPageTableEntry};

verus! {

/// We assume that the available physical memory is 1 to MAX_FRAME_NUM - 1.
pub const MAX_FRAME_NUM: usize = 10000;

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
            self.allocated_addrs.contains(addr) ==> 1 <= addr < MAX_FRAME_NUM as int && addr
                % PAGE_SIZE() as int == 0
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
        res.0.addr() < MAX_FRAME_NUM * PAGE_SIZE(),
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
            1 <= i < MAX_FRAME_NUM ==> {
                if let Some((p, _)) = self.frames[i as int] {
                    p.addr() == i * PAGE_SIZE()
                } else {
                    true
                }
            }
            // The zero frame is reserved for the kernel.
             && self.frames[0].unwrap().0.addr() == 0
    }

    #[verifier::external_body]
    pub fn init() -> MockGlobalAllocator {
        let mut frames = [const { None };MAX_FRAME_NUM];

        for i in 0..MAX_FRAME_NUM {
            let pptr = PPtr::<MockPageTablePage>::from_addr(i * PAGE_SIZE());
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
            exists|i: usize| 1 <= i < MAX_FRAME_NUM && old(self).frames[i as int].is_some(),
        ensures
            res.1@.pptr() == res.0,
            res.0.addr() < MAX_FRAME_NUM,
            forall|i: usize|
                0 <= i < MAX_FRAME_NUM ==> {
                    if self.frames[i as int].is_some() {
                        self.frames[i as int].unwrap().1@.pptr() == self.frames[i as int].unwrap().0
                    } else {
                        true
                    }
                },
    {
        for i in 1..MAX_FRAME_NUM {
            if !self.frames[i].is_none() {
                let (p, pt) = self.frames[i].take().unwrap();
                return (p, pt);
            }
        }
        vpanic!("No available frames");
    }
}

} // verus!
