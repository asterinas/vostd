#![cfg_attr(verus_keep_ghost, verus::trusted)]

// trusted: these are used in trusted definitions
//
// `overlap_sanity_check` hardens a spec, so we don't count it as trusted

use vstd::prelude::*;

use crate::spec::mmu;

verus! {

///从右往左数(从0开始)第`low`位到第`high`位的位掩码
macro_rules! bitmask_inc {
    ($low:expr,$high:expr) => {
        (!(!0usize << (($high+1usize)-$low))) << $low
    }
}

pub(crate) use bitmask_inc;

///从右往左数(从0开始)第`v`位的位掩码
macro_rules! bit {
    ($v:expr) => {
        1usize << $v
    }
}

pub(crate) use bit;

pub const X86_NUM_LAYERS: usize = 4;

pub const X86_NUM_ENTRIES: usize = 512;

// The maximum physical address width is between 32 and 52 bits.
#[verifier(external_body)]
pub const MAX_PHYADDR_WIDTH: usize = 52;

pub axiom fn axiom_max_phyaddr_width_facts()
    ensures
        32 <= MAX_PHYADDR_WIDTH <= 52,
;

// We cannot use a dual exec/spec constant for MAX_PHYADDR, because for those Verus currently
// doesn't support manually guiding the no-overflow proofs.
pub spec const MAX_PHYADDR_SPEC: usize = ((1usize << MAX_PHYADDR_WIDTH) - 1usize) as usize;

#[verifier::when_used_as_spec(MAX_PHYADDR_SPEC)]
pub exec const MAX_PHYADDR: usize
    ensures
        MAX_PHYADDR == MAX_PHYADDR_SPEC,
{
    proof {
        axiom_max_phyaddr_width_facts();
    }
    assert(1usize << 32 == 0x100000000) by (compute);
    assert(forall|m: usize, n: usize| n < m < 64 ==> 1usize << n < 1usize << m) by (bit_vector);
    (1usize << MAX_PHYADDR_WIDTH) - 1usize
}

pub const WORD_SIZE: usize = 8;

pub const PAGE_SIZE: usize = 4096;

pub spec const X86_MAX_ENTRY_SIZE: nat = 512 * 512 * 512 * 4096;

pub spec const MAX_BASE: nat = X86_MAX_ENTRY_SIZE * (X86_NUM_ENTRIES as nat);

///某一级页表的一个表项（entry）所映射的虚拟地址空间大小
pub const L3_ENTRY_SIZE: usize = PAGE_SIZE;

pub const L2_ENTRY_SIZE: usize = 512 * L3_ENTRY_SIZE;

pub const L1_ENTRY_SIZE: usize = 512 * L2_ENTRY_SIZE;

pub const L0_ENTRY_SIZE: usize = 512 * L1_ENTRY_SIZE;

///根据地址偏移量和entry_size算index
pub open spec fn index_from_offset(offset: nat, entry_size: nat) -> (res: nat)
    recommends
        entry_size > 0,
{
    offset / entry_size
}

//根据两个地址和entry_size算index
pub open spec fn index_from_base_and_addr(base: nat, addr: nat, entry_size: nat) -> nat
    recommends
        addr >= base,
        entry_size > 0,
{
    index_from_offset(sub(addr, base), entry_size)
}

//根据基地址、索引和entry_size算entry的基地址
pub open spec fn entry_base_from_index(base: nat, idx: nat, entry_size: nat) -> nat {
    base + idx * entry_size
}

//根据基地址、索引和entry_size算下一个entry的基地址
pub open spec fn next_entry_base_from_index(base: nat, idx: nat, entry_size: nat) -> nat {
    base + (idx + 1) * entry_size
}

//基地址加上PTE映射的大小小于最大虚拟地址
pub open spec fn candidate_mapping_in_bounds(base: nat, pte: PTE) -> bool {
    base + pte.frame.size < x86_arch_spec.upper_vaddr(0, 0)
}

pub open spec fn candidate_mapping_in_bounds_pmem(c: mmu::Constants, pte: PTE) -> bool {
    pte.frame.base + pte.frame.size <= c.range_mem.1
}

// TODO: maybe we can deduplicate these two definitions somehow
pub open spec fn candidate_mapping_overlaps_existing_vmem_usize(
    mappings: Map<usize, PTE>,
    base: usize,
    pte: PTE,
) -> bool {
    exists|b: usize|
        #![auto]
        {
            &&& mappings.contains_key(b)
            &&& overlap(
                MemRegion { base: base as nat, size: pte.frame.size },
                MemRegion { base: b as nat, size: mappings[b].frame.size },
            )
        }
}

pub open spec fn candidate_mapping_overlaps_existing_vmem(
    mappings: Map<nat, PTE>,
    base: nat,
    pte: PTE,
) -> bool {
    exists|b: nat|
        {
            &&& #[trigger] mappings.contains_key(b)
            &&& overlap(
                MemRegion { base: base, size: pte.frame.size },
                MemRegion { base: b, size: mappings[b].frame.size },
            )
        }
}

pub open spec fn candidate_mapping_overlaps_existing_pmem(
    mappings: Map<nat, PTE>,
    pte: PTE,
) -> bool {
    exists|b: nat|
        #![auto]
        {
            &&& mappings.dom().contains(b)
            &&& overlap(pte.frame, mappings.index(b).frame)
        }
}

pub open spec(checked) fn align_to_usize(a: usize, b: usize) -> usize {
    sub(a, a % b)
}

pub open spec(checked) fn aligned(addr: nat, size: nat) -> bool {
    addr % size == 0
}

pub open spec fn between(x: nat, a: nat, b: nat) -> bool {
    a <= x && x < b
}

pub open spec fn new_seq<T>(i: nat, e: T) -> Seq<T>
    decreases i,
{
    if i == 0 {
        seq![]
    } else {
        new_seq((i - 1) as nat, e).push(e)
    }
}

#[derive(Copy, Clone)]
pub struct Core {
    pub node_id: nat,
    pub core_id: nat,
}

pub enum LoadResult {
    Pagefault,
    Value(Seq<u8>),
}

pub enum StoreResult {
    Pagefault,
    Ok,
}

#[allow(inconsistent_fields)]
pub enum MemOp {
    Load { is_exec: bool, size: nat, result: LoadResult },
    Store { new_value: Seq<u8>, result: StoreResult },
}

impl MemOp {
    pub open spec fn is_pagefault(self) -> bool {
        ||| self matches MemOp::Load { result: LoadResult::Pagefault, .. }
        |  || self matches MemOp::Store { result: StoreResult::Pagefault, .. }
    }

    pub open spec fn op_size(self) -> nat {
        match self {
            MemOp::Load { size, .. } => size,
            MemOp::Store { new_value, .. } => new_value.len(),
        }
    }

    pub open spec fn valid_op_size(self) -> bool {
        ||| self.op_size() == 1
        ||| self.op_size() == 2
        ||| self.op_size() == 4
        ||| self.op_size() == 8
    }
}

///由基地址和长度组成
pub struct MemRegion {
    pub base: nat,
    pub size: nat,
}

impl MemRegion {
    pub open spec fn contains(self, addr: nat) -> bool {
        between(addr, self.base, self.base + self.size)
    }
}

pub open spec fn overlap(region1: MemRegion, region2: MemRegion) -> bool {
    if region1.base <= region2.base {
        region1.base == region2.base || region2.base < region1.base + region1.size
    } else {
        region1.base < region2.base + region2.size
    }
}

// hardens spec for overlap
#[verus::line_count::ignore]
proof fn overlap_sanity_check() {
    assert(overlap(MemRegion { base: 0, size: 4096 }, MemRegion { base: 0, size: 4096 }));
    assert(overlap(MemRegion { base: 0, size: 8192 }, MemRegion { base: 0, size: 4096 }));
    assert(overlap(MemRegion { base: 0, size: 4096 }, MemRegion { base: 0, size: 8192 }));
    assert(overlap(MemRegion { base: 0, size: 8192 }, MemRegion { base: 4096, size: 4096 }));
    assert(!overlap(MemRegion { base: 4096, size: 8192 }, MemRegion { base: 0, size: 4096 }));
    assert(!overlap(MemRegion { base: 0, size: 4096 }, MemRegion { base: 8192, size: 16384 }));
}

#[derive(Copy, Clone)]
pub struct MemRegionExec {
    pub base: usize,
    pub size: usize,
}

impl MemRegionExec {
    pub open spec fn view(self) -> MemRegion {
        MemRegion { base: self.base as nat, size: self.size as nat }
    }
}

#[derive(Copy, Clone)]
pub struct Flags {
    pub is_writable: bool,
    pub is_supervisor: bool,
    pub disable_execute: bool,
}

pub struct PTE {
    pub frame: MemRegion,
    /// The `flags` field on a `PTE` denotes the combined flags of the entire
    /// translation path to the entry. (See page table walk definition in hardware model,
    /// `spec_t::hardware`.) However, because we always set the flags on directories to be
    /// permissive these flags also correspond to the flags that we set for the frame mapping
    /// corresponding to this `PTE`.
    pub flags: Flags,
}

#[derive(Copy, Clone)]
pub struct PageTableEntryExec {
    pub frame: MemRegionExec,
    pub flags: Flags,
}

impl PageTableEntryExec {
    pub open spec fn view(self) -> PTE {
        PTE { frame: self.frame@, flags: self.flags }
    }
}

impl Flags {
    pub open spec fn from_bits(flag_RW: bool, flag_US: bool, flag_XD: bool) -> Flags {
        Flags { is_writable: flag_RW, is_supervisor: !flag_US, disable_execute: flag_XD }
    }

    pub open spec fn combine(self, other: Flags) -> Flags {
        Flags {
            is_writable: self.is_writable && other.is_writable,
            is_supervisor: self.is_supervisor || other.is_supervisor,
            disable_execute: self.disable_execute || other.disable_execute,
        }
    }
}

pub ghost struct ArchLayer {
    /// Address space size mapped by a single entry at this layer
    pub entry_size: nat,
    /// Number of entries at this layer
    /// 一个页表页里的页表项数量
    pub num_entries: nat,
}

pub ghost struct Arch {
    pub layers: Seq<ArchLayer>,
    // [512G, 1G  , 2M  , 4K  ]
    // [512 , 512 , 512 , 512 ]
}

impl Arch {
    ///返回第`layer`层单个entry映射的地址空间大小
    pub open spec(checked) fn entry_size(self, layer: nat) -> nat
        recommends
            layer < self.layers.len(),
    {
        self.layers[layer as int].entry_size
    }

    pub open spec(checked) fn num_entries(self, layer: nat) -> nat
        recommends
            layer < self.layers.len(),
    {
        self.layers.index(layer as int).num_entries
    }

    ///给定层和基地址，返回该层的最大虚拟地址（应该取不到，因为num_entries是512）
    pub open spec(checked) fn upper_vaddr(self, layer: nat, base: nat) -> nat
        recommends
            self.inv(),
            layer < self.layers.len(),
    {
        self.entry_base(layer, base, self.num_entries(layer))
    }

    pub open spec(checked) fn inv(&self) -> bool {
        &&& self.layers.len() <= X86_NUM_LAYERS
        &&& forall|i: nat|
            #![trigger self.entry_size(i)]
            #![trigger self.num_entries(i)]
            i < self.layers.len() ==> {
                &&& 0 < self.entry_size(i) <= X86_MAX_ENTRY_SIZE
                &&& 0 < self.num_entries(i) <= X86_NUM_ENTRIES
                &&& self.entry_size_is_next_layer_size(i)
            }
    }

    ///第i层单个entry映射的地址空间大小等于下一层的entry size乘以下一层单个页表页的entry数量
    pub open spec(checked) fn entry_size_is_next_layer_size(self, i: nat) -> bool
        recommends
            i < self.layers.len(),
    {
        i + 1 < self.layers.len() ==> self.entry_size(i) == self.entry_size((i + 1) as nat)
            * self.num_entries((i + 1) as nat)
    }

    ///存在某一大于等于`min_idx`的索引`i`，使得第`i`层的entry size等于给定的entry size
    pub open spec(checked) fn contains_entry_size_at_index_atleast(
        &self,
        entry_size: nat,
        min_idx: nat,
    ) -> bool {
        exists|i: nat|
            min_idx <= i < self.layers.len() && #[trigger] self.entry_size(i) == entry_size
    }

    ///存在某一索引`i`，使得第`i`层的entry size等于给定的entry size
    pub open spec(checked) fn contains_entry_size(&self, entry_size: nat) -> bool {
        self.contains_entry_size_at_index_atleast(entry_size, 0)
    }

    ///给定层和基地址和某个虚拟地址，返回该虚拟地址在该层的索引
    #[verifier(inline)]
    pub open spec(checked) fn index_for_vaddr(self, layer: nat, base: nat, vaddr: nat) -> nat
        recommends
            self.inv(),
            layer < self.layers.len(),
            base <= vaddr,
    {
        index_from_base_and_addr(base, vaddr, self.entry_size(layer))
    }

    ///给定层和基地址，返回该层第idx个entry的基地址
    #[verifier(inline)]
    pub open spec(checked) fn entry_base(self, layer: nat, base: nat, idx: nat) -> nat
        recommends
            self.inv(),
            layer < self.layers.len(),
    {
        // base + idx * self.entry_size(layer)
        entry_base_from_index(base, idx, self.entry_size(layer))
    }

    #[verifier(inline)]
    pub open spec(checked) fn next_entry_base(self, layer: nat, base: nat, idx: nat) -> nat
        recommends
            self.inv(),
            layer < self.layers.len(),
    {
        // base + (idx + 1) * self.entry_size(layer)
        next_entry_base_from_index(base, idx, self.entry_size(layer))
    }
}

pub struct ArchLayerExec {
    /// Address space size mapped by a single entry at this layer
    pub entry_size: usize,
    /// Number of entries of at this layer
    pub num_entries: usize,
}

pub struct ArchExec {
    pub layers: [ArchLayerExec; 4],
}

/*
pub exec const x86_arch_exec: ArchExec ensures x86_arch_exec@ == x86_arch_spec {
    let layers = [
        ArchLayerExec { entry_size: L0_ENTRY_SIZE, num_entries: 512 },
        ArchLayerExec { entry_size: L1_ENTRY_SIZE, num_entries: 512 },
        ArchLayerExec { entry_size: L2_ENTRY_SIZE, num_entries: 512 },
        ArchLayerExec { entry_size: L3_ENTRY_SIZE, num_entries: 512 },
    ];
    assert(x86_arch_spec.layers =~= layers@.map(|n,e:ArchLayerExec| e@));
    ArchExec { layers }
}*/

pub spec const x86_arch_spec: Arch = Arch {
    layers: seq![
        ArchLayer { entry_size: L0_ENTRY_SIZE as nat, num_entries: 512 },
        ArchLayer { entry_size: L1_ENTRY_SIZE as nat, num_entries: 512 },
        ArchLayer { entry_size: L2_ENTRY_SIZE as nat, num_entries: 512 },
        ArchLayer { entry_size: L3_ENTRY_SIZE as nat, num_entries: 512 },
    ],
};

pub proof fn x86_arch_spec_upper_bound()
    ensures
        x86_arch_spec.upper_vaddr(0, 0) == 512 * 512 * 1024 * 1024 * 1024,
        x86_arch_spec.upper_vaddr(0, 0) == MAX_BASE,
{
    assert(x86_arch_spec.upper_vaddr(0, 0) == 512 * 512 * 1024 * 1024 * 1024) by (compute_only);
    assert(x86_arch_spec.upper_vaddr(0, 0) == MAX_BASE) by (compute_only);
}

pub proof fn lemma_x86_arch_spec_inv()
    ensures
        x86_arch_spec.inv(),
{
}

pub open spec fn nat_keys<V>(m: Map<usize, V>) -> Map<nat, V> {
    Map::new(|k: nat| k <= usize::MAX && m.contains_key(k as usize), |k: nat| m[k as usize])
}

pub open spec fn usize_keys<V>(m: Map<nat, V>) -> Map<usize, V>
    recommends
        forall|k| m.contains_key(k) ==> k <= usize::MAX,
{
    Map::new(|k: usize| m.contains_key(k as nat), |k: usize| m[k as nat])
}

pub open spec fn update_range<A>(s: Seq<A>, idx: int, new: Seq<A>) -> Seq<A> {
    s.subrange(0, idx) + new + s.subrange(idx + new.len(), s.len() as int)
}

} // verus!
