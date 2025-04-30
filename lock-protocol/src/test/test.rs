pub type Paddr = usize;

#[derive(Clone, Copy)]
pub struct PteFlag;

#[derive(Clone, Copy)]
pub struct PageTableEntry {
    pub frame_pa: Paddr,
    pub flags: PteFlag,

    // TODO: this should not be here, just for testing {
    pub level: usize, // this should not be here, just for testing
                      // pub children_addr: Paddr, // this should not be here, just for testing
                      // }
}

#[derive(Clone)]
pub struct Frame {
    pub pa: Paddr,
    pub ptes: [PageTableEntry; 512],
}

#[derive(Copy, Clone)]
pub struct SimplePageTableEntry {
    pub paddr: Paddr,
    pub frame_pa: Paddr,
    pub level: usize,
    // pub prop: PageProperty,
}

fn main() {
    println!(
        "size of PageTableEntry: {}",
        core::mem::size_of::<PageTableEntry>()
    );
    println!("size of Frame: {}", core::mem::size_of::<Frame>());
    println!(
        "size of SimplePageTableEntry: {}",
        core::mem::size_of::<SimplePageTableEntry>()
    );

    use std::collections::HashMap;

    let map = HashMap::from([("a", 1), ("b", 2), ("c", 3)]);

    for key in map.keys() {
        println!("{key}");
    }
    let keys = map.keys();
    println!("{:?}", keys);
}
