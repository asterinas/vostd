# MetaSlot: Frame Metadata Container

`MetaSlot` is the fundamental data structure that stores metadata for each physical memory frame in the Asterinas system. Think of it as a "metadata header" that provides both frame management and type-safe metadata storage.

## MetaSlot Structure

```rust
pub struct MetaSlot {
    pub storage: PPtr<MetaSlotStorage>,     // Pointer to actual metadata
    pub ref_count: PAtomicU64,              // Atomic reference counter
    pub vtable_ptr: PPtr<usize>,            // Virtual table pointer for type info
    pub in_list: PAtomicU64,                // Linked list membership tracking
}
```

**Size**: Fixed 64 bytes per frame (verified by Verus)

## MetaSlot vs MetaSlotStorage - Physical vs Logical Separation

**IMPORTANT**: MetaSlot and MetaSlotStorage are at **different physical memory locations**:

### MetaSlot (Management Header)
- **Purpose**: Frame management infrastructure 
- **Contains**: Reference counting, type information, list membership
- **Physical Location**: Fixed offset from frame address (computed by `frame_to_meta()`)
- **Lifetime**: Exists for every physical frame
- **Contains Pointer**: `storage: PPtr<MetaSlotStorage>` points to the actual content

### MetaSlotStorage (Content Data)
- **Purpose**: Actual frame metadata content
- **Contains**: Frame-specific data based on usage  
- **Physical Location**: Separate memory location, **pointed to** by `MetaSlot::storage`
- **Lifetime**: Created/destroyed with frame allocation/deallocation

### However: MetaSlotStorage vs High-Level Types (Same Physical Location)

**YES** - `MetaSlotStorage` and high-level types like `Link<M>` are the **same physical memory** but with **different interpretations**:

```rust
// Same physical bytes, different interpretations:
MetaSlotStorage::FrameLink(StoredLink {     // Low-level storage view
    next: Some(0x1000),
    prev: None, 
    slot: MetaSlotInner { ... }
})
    ↕ ReprPtr casting (zero-cost)
Link<M> {                                   // High-level typed view  
    next: Some(ReprPtr(0x1000)),
    prev: None,
    meta: M { ... }
}
```

This is what `ReprPtr<MetaSlotStorage, Link<M>>` enables - safe reinterpretation of the same memory bytes.

```rust
pub enum MetaSlotStorage {
    Empty([u8; 39]),                           // Unused/default state
    FrameLink(StoredLink),                     // For linked list frames  
    PTNode(StoredPageTablePageMeta),           // For page table node frames
    // Can be extended with more variants
}
```

## Memory Layout

```
Physical Frame (4KB)
┌─────────────────┐ ← Frame data
│                 │
│   Frame Data    │ 
│                 │
├─────────────────┤ ← Computed metadata address
│    MetaSlot     │ ── 64 bytes ──┐
│  ┌─────────────┬┤                │
│  │ storage  ───┼┤────────────────┼──┐
│  │ ref_count   ││                │  │
│  │ vtable_ptr  ││                │  │  
│  │ in_list     ││                │  │
│  └─────────────┴┤                │  │
├─────────────────┤                │  │
│                 │                │  │
│   Other Meta    │                │  │
│    Slots        │                │  │
└─────────────────┘                │  │
                                   │  │
    MetaSlotStorage                │  │
┌─────────────────┐ ←──────────────────┘
│ FrameLink(      │                │
│   StoredLink {  │                │
│     next: addr, │                │
│     prev: addr, │                │ 
│     slot: ...   │                │
│   }             │                │
│ )               │                │
└─────────────────┘ ←──────────────┘
```

## Type-Safe Metadata Access

The `ReprPtr<MetaSlotStorage, T>` system enables safe casting:

```rust
impl MetaSlot {
    pub fn cast_storage<T: Repr<MetaSlotStorage>>(
        &self,
        addr: usize,
        Tracked(owner): Tracked<&MetaSlotOwner>,
    ) -> ReprPtr<MetaSlotStorage, T>
}
```

**Example**: `ReprPtr<MetaSlotStorage, Link<M>>`
- Raw storage: `MetaSlotStorage::FrameLink(StoredLink { ... })`
- Interpreted as: `Link<M> { next, prev, meta }`

## Frame Lifecycle Integration

The `MetaSlot` participates in the frame state machine:

1. **Reference Counting**: `ref_count` tracks frame ownership
   - `REF_COUNT_UNUSED` (u64::MAX) = available
   - `REF_COUNT_UNIQUE` (u64::MAX-1) = exclusively owned
   - `1..REF_COUNT_MAX` = reference counted

2. **Type Safety**: `vtable_ptr` enables runtime type checking
3. **List Management**: `in_list` prevents frames from being in multiple lists
4. **Storage Management**: `storage` points to typed metadata

## Key Design Principles

### 1. **Separation of Concerns**
```rust
// Management (MetaSlot) vs Content (MetaSlotStorage)
let slot: &MetaSlot = get_frame_slot(paddr);           // Management
let link: Link<M> = slot.cast_storage(addr).take(...); // Content
```

### 2. **Type Safety**
```rust
// Cannot cast PTNode storage to Link metadata
match storage {
    MetaSlotStorage::FrameLink(_) => /* OK for Link<M> */,
    MetaSlotStorage::PTNode(_) => /* Wrong type! */,
    _ => /* Invalid */,
}
```

### 3. **Memory Efficiency** 
- Fixed 64-byte slots enable O(1) address computation
- No heap allocation for metadata storage
- Direct pointer arithmetic: `frame_paddr → metadata_vaddr`

## Usage Patterns

### Frame Allocation
```rust
// 1. Get MetaSlot for frame
let slot = get_slot(paddr)?;

// 2. Initialize storage with specific metadata type
let storage = MetaSlotStorage::FrameLink(StoredLink { ... });

// 3. Set up reference counting and type info
slot.ref_count.store(1);
slot.vtable_ptr.store(Link::<M>::vtable_ptr());
```

### Type-Safe Access
```rust
// 1. Cast storage to expected type
let link_ptr: ReprPtr<MetaSlotStorage, Link<M>> = 
    slot.cast_storage(addr, owner);

// 2. Access with verification
let link: Link<M> = link_ptr.take(permissions);
let metadata: M = link.meta;
```

### Reference Management
```rust
// Clone frame handle
slot.ref_count.fetch_add(1);

// Drop frame handle  
let old_count = slot.ref_count.fetch_sub(1);
if old_count == 1 {
    // Last reference - deallocate
    slot.drop_storage_in_place();
    slot.ref_count.store(REF_COUNT_UNUSED);
}
```

`MetaSlot` thus provides the essential infrastructure that enables safe, efficient, and type-aware frame metadata management in the Asterinas memory system.
