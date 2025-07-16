use vstd::prelude::*;

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
pub ghost struct AllocatorModel {
    pub allocated_addrs: Set<int>,
}

impl AllocatorModel {
    pub fn new() -> AllocatorModel {
        AllocatorModel {
            allocated_addrs: Set::empty(),
        }
    }

    pub open spec fn invariants(&self) -> bool {
        forall|addr: int| #[trigger]
            self.allocated_addrs.contains(addr) ==> 1 <= addr < MAX_FRAME_NUM as int && addr
                % PAGE_SIZE as int == 0
    }
}

pub fn alloc_page_table(model: &mut AllocatorModel) -> (res: (
    PPtr<MockPageTablePage>,
    Tracked<PointsTo<MockPageTablePage>>,
))
    requires
        old(model).invariants(),
    ensures
        res.1@.pptr() == res.0,
        res.0.addr() < MAX_FRAME_NUM * PAGE_SIZE,
        model.invariants(),
        !old(model).allocated_addrs.contains(res.0.addr() as int),
        model.allocated_addrs.contains(res.0.addr() as int),
{
    let (mut allocator, write_handle) = GLOBAL_ALLOCATOR.acquire_write();

    // Initialize if not initialized.
    if allocator.is_none() {
        *allocator = Some(MockGlobalAllocator::init());
    }
    let (p, pt) = allocator.as_mut().unwrap().alloc();

    write_handle.release_write(allocator);

    (p, pt)
}

struct MockGlobalAllocator {
    pub frames: [Option<
        (PPtr<MockPageTablePage>, Tracked<PointsTo<MockPageTablePage>>),
    >; MAX_FRAME_NUM],
}

static GLOBAL_ALLOCATOR: RwLock<
    Option<MockGlobalAllocator>,
    spec_fn(Option<MockGlobalAllocator>) -> bool,
> = RwLock::new(None, Ghost(|v: Option<MockGlobalAllocator>| global_allocator_invariants(v@)));

pub open spec fn global_allocator_invariants(v: Option<MockGlobalAllocator>) -> bool {
    match v {
        None => true,
        Some(ga) => ga.invariants(),
    }
}

impl MockGlobalAllocator {
    pub closed spec fn invariants(&self) -> bool {
        forall|i: usize|
            1 <= i < MAX_FRAME_NUM ==> {
                if let Some((p, _)) = self.frames[i] {
                    p.addr() == i * PAGE_SIZE
                } else {
                    true
                }
            }
            // The zero frame is reserved for the kernel.
             && self.frames[0].as_ref().unwrap().0.addr() == 0
    }

    #[verifier::external_body]
    pub fn init() -> MockGlobalAllocator {
        let mut frames = [None;MAX_FRAME_NUM];

        for i in 0..MAX_FRAME_NUM {
            let pptr = PPtr::<MockPageTableEntry>::from_addr(i * PAGE_SIZE).read(
                Tracked::assume_new(),
            );
            let points_to = Tracked(PointsTo::new(pptr));
            frames[i] = Some((pptr, points_to));
        }

        MockGlobalAllocator { frames }
    }

    #[verifier::external_body]
    pub fn alloc(&mut self) -> (res: (
        PPtr<MockPageTablePage>,
        Tracked<PointsTo<MockPageTablePage>>,
    ))
        requires
            self.frames.iter().any(|f| !f.is_none()),
        ensures
            res.1@.pptr() == res.0,
            res.0.addr() < MAX_FRAME_NUM,
            forall|i: usize|
                0 <= i < MAX_FRAME_NUM ==> {
                    if self.frames[i].is_some() {
                        self.frames[i].unwrap().1@.pptr() == self.frames[i].unwrap().0
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
