# Design Plan: VmSpace, VmReader, VmWriter with VirtPtr

## Objective
Design and implement `VmSpace`, `VmReader`, and `VmWriter` using `VirtPtr` to ensure that:
1.  No arbitrary read/write can occur.
2.  `VmReader`/`VmWriter` must occur within a well-formed `VmSpace`.
3.  Memory accesses are verified safe using `MemView`.

## Core Abstractions

### 1. `VirtPtr` (Existing in `vstd_extra/src/virtual_ptr.rs`)
*   **Role**: Represents a virtual pointer with ghost range information.
*   **Fields**:
    *   `vaddr: usize`: The executable virtual address.
    *   `range: Ghost<Range<usize>>`: The validity range of the pointer.
*   **Operations**: `read`, `write`, `read_offset`, etc., which require `Tracked<MemView>`.

### 2. `MemView` (Existing in `vstd_extra/src/virtual_ptr.rs`)
*   **Role**: Models the state of memory (mappings and contents).
*   **Fields**:
    *   `mappings`: Set of virtual-to-physical mappings.
    *   `memory`: Map of physical addresses to values.

### 3. `VmSpace` / `VmSpaceOwner` (in `ostd/src/mm/vm_space.rs`)
*   **Role**: Manages the virtual address space and ownership of `MemView`.
*   **Changes**:
    *   `VmSpaceOwner` will hold the `MemView` (or a `Map<usize, MemContents>` representing it) in its ghost state.
    *   It maintains the invariant that the Page Table state matches the `MemView`.

### 4. `VmReader` / `VmWriter` (in `ostd/src/mm/io.rs`)
*   **Role**: Safe interfaces for memory access.
*   **Changes**:
    *   Replace `cursor: PPtr<u8>` and `end: PPtr<u8>` with `cursor: VirtPtr` and `end: VirtPtr`.
    *   Maintain invariants linking `cursor` to `VmIoOwner`.

### 5. `VmIoOwner` (in `ostd/src/mm/io.rs`)
*   **Role**: Represents exclusive/shared access to a memory range.
*   **Changes**:
    *   Link to `MemView`.
    *   For `VmWriter` (exclusive), it might hold a "fragment" of the `MemView` (permissions to write).
    *   For `VmReader` (shared/read-only), it might hold a read permission or snapshot.
    *   However, to support simpler interaction with `VmSpaceOwner`, `VmIoOwner` might just track the *range* and *validity*, while `VmSpaceOwner` (or a passed `MemView` token) provides the content access.

## Detailed Design

### Struct Updates

#### `VmReader`
```rust
pub struct VmReader<'a> {
    pub cursor: VirtPtr,
    pub end: VirtPtr,
    pub phantom: PhantomData<&'a [u8]>,
}
```

#### `VmWriter`
```rust
pub struct VmWriter<'a> {
    pub cursor: VirtPtr,
    pub end: VirtPtr,
    pub phantom: PhantomData<&'a [u8]>,
}
```

### Invariants & Safety

1.  **Creation**:
    *   `VmSpace::reader(vaddr, len)`:
        *   Checks `vaddr` and `len` against user space bounds.
        *   Constructs `VirtPtr { vaddr, range: Ghost(vaddr..vaddr+len) }`.
        *   Returns `VmReader` initialized with this `VirtPtr`.
        *   **Verification**: Requires `VmSpaceOwner` to prove that the range is mapped and accessible.

2.  **Memory Access**:
    *   `VmReader::read_val<T>()`:
        *   Requires `self.cursor` is valid in `VmIoOwner`.
        *   Requires access to `MemView` (passed via `Tracked` argument or implied by `VmIoOwner`?).
        *   Since `VmIoOwner` is usually passed to `read/write`, `VmIoOwner` should probably carry the necessary ghost permissions (`MemView` fragment) to satisfy `VirtPtr::read/write`.

3.  **Kernel vs User Space**:
    *   `VirtPtr` unifies them. `MemView` can represent kernel mappings (identity mapped or otherwise) and user mappings.
    *   `VmReader::from_kernel_space`: Constructs `VirtPtr` with kernel range. `MemView` for kernel is needed.

### Interaction with `VmSpace`

*   `VmSpaceOwner` invariant:
    *   Holds `MemView`.
    *   `readers` and `writers` disjoint ranges.
    *   The `MemView` is consistent with the `PageTable`.

### Preventing Arbitrary Access

*   `VirtPtr::read/write` preconditions require `MemView` translation to succeed.
*   `VmReader/Writer` encapsulate `VirtPtr`.
*   User code only gets `VmReader/Writer` from `VmSpace` (validated) or `from_kernel_space` (unsafe/validated).
*   Therefore, only valid ranges can be accessed.

## Implementation Plan

1.  **Phase 1: Struct Refactoring**
    *   Update `VmReader`/`VmWriter` in `ostd/src/mm/io.rs` to use `VirtPtr`.
    *   Update `impl` blocks to match.

2.  **Phase 2: VmSpace Integration**
    *   Update `VmSpace::reader/writer` in `ostd/src/mm/vm_space.rs` to construct `VirtPtr`.
    *   Ensure `VmSpaceOwner` tracks necessary state.

3.  **Phase 3: Verification Logic**
    *   Implement/Stub `VirtPtr` methods in `VmReader` operations.
    *   Ensure proofs verify.

4.  **Phase 4: Safety Checks**
    *   Review `from_user_space` safety comments.
    *   Ensure `VirtPtr` invariants are upheld.

## Design Rationale (Q&A)

### Q1: Why do `VmReader`/`VmWriter` need `cursor` and `end` if `VirtPtr` already carries range information?

**Answer**:
1.  **Ghost vs Executable**: The `range` field in `VirtPtr` is a **ghost** field (`Ghost<Range<usize>>`), meaning it exists only during verification and is erased at runtime. `VmReader` and `VmWriter` need to perform runtime checks (e.g., in `remain()`, `read()`) to prevent out-of-bounds access. Therefore, they must store the `end` address (or length) as an **executable** field (`usize` or `VirtPtr` wrapping `usize`).
2.  **Cursor Movement**: `VmReader` represents a sliding window over a buffer. `cursor` points to the current position, which advances as data is read. `end` marks the boundary. While `VirtPtr` at `cursor` knows it is valid up to `range.end` (ghostly), the runtime code needs `end` to calculate `copy_len` and ensure safety dynamically.

### Q2: How do we ensure that memories are mapped and no alias occurs?

**Answer**:

**1. Ensuring Mapped Memory**:
*   **`MemView` Authority**: The `VmSpaceOwner` holds the authoritative `MemView`, which contains the set of valid virtual-to-physical `mappings`.
*   **Proof at Creation**: When a `VmReader` or `VmWriter` is created via `VmSpace::reader/writer`, the caller must provide a proof (checked against `VmSpaceOwner`) that the requested virtual address range is fully covered by valid `mappings` in the `MemView`.
*   **Continuous Validity**: The `VirtPtr` used by `VmReader` carries a ghost `range` that is proven to be within the mapped regions. Operations like `VirtPtr::read` have preconditions requiring the address to translate successfully in the `MemView`.

**2. Ensuring No Aliasing**:
*   **Tracking Active IOs**: `VmSpaceOwner` maintains two maps: `readers` and `writers`, which track all active `VmIoOwner` instances.
*   **Disjointness Invariants**: The `VmSpaceOwner` invariant enforces strict aliasing rules:
    *   **Writers are Exclusive**: Every writer in the `writers` map must be disjoint from all other writers AND all readers.
    *   **Readers vs Writers**: Readers must be disjoint from writers.
    *   *(Note: Readers may overlap with other readers, allowing shared read access, provided the implementation supports it. If current implementation enforces reader disjointness, it satisfies "no mutable alias" trivially.)*
    *   **Ownership Semantics**: To create a `VmWriter`, one must obtain an exclusive "loan" of the range from `VmSpaceOwner`, which updates the `writers` map. This fails if any overlapping reader or writer exists, guaranteeing no aliasing.

### Q3: How does a `VmSpaceOwner` look like, and how do we ensure it is mapped? What is the invariant?

**Answer**:

**1. Structure of `VmSpaceOwner`**:
It tracks the page table state, the abstract memory view, and all active IO permissions.

```rust
pub tracked struct VmSpaceOwner<'a> {
    /// The owner of the page table (tracks hardware page table state).
    pub page_table_owner: PageTableOwner<'a, UserPtConfig>,
    
    /// The abstract view of memory (ghost state).
    /// Models what is actually mapped and the memory contents.
    pub mem_view: MemView, 
    
    /// Active readers (shared access).
    pub readers: Map<nat, VmIoOwner<'a>>,
    
    /// Active writers (exclusive access).
    pub writers: Map<nat, VmIoOwner<'a>>,
    
    /// Whether this VM space is currently active on the CPU.
    pub active: bool,
}
```

**2. Ensuring Mapped**:
*   The **Consistency Invariant** (see below) ensures that `mem_view` faithfully reflects the `page_table_owner`. If the page table says a page is present, `mem_view` has a mapping for it.
*   When creating a `VmReader` (safe), the precondition requires that the range is covered by `mem_view.mappings`. Since `mem_view` is tied to the page table by invariant, this guarantees the hardware page table also has the mapping.

**3. The Invariant**:
```rust
impl<'a> Inv for VmSpaceOwner<'a> {
    open spec fn inv(self) -> bool {
        // 1. Component invariants
        &&& self.page_table_owner.inv()
        
        // 2. Consistency: MemView must match Page Table
        // The mappings in MemView must correspond to valid entries in the Page Table.
        // (This ensures that if we think it's mapped in ghost state, it's mapped in hardware).
        &&& self.page_table_owner.matches_view(self.mem_view)
        
        // 3. Disjointness of Readers/Writers
        &&& self.readers.dom().finite()
        &&& self.writers.dom().finite()
        &&& self.active ==> {
             &&& self.readers.dom().disjoint(self.writers.dom())
             // Writers are mutually disjoint
             &&& forall|i, j, w1, w2| ...
             // Readers are disjoint from writers
             &&& forall|i, j, r, w| ...
        }
        
        // 4. Validity of IO Owners
        // Every active reader/writer must correspond to a valid mapped region in MemView.
        &&& forall|i, reader| self.readers.contains(i, reader) ==> {
             reader.inv() && 
             self.mem_view.covers_range(reader.range)
        }
        &&& forall|i, writer| self.writers.contains(i, writer) ==> {
             writer.inv() && 
             self.mem_view.covers_range(writer.range)
        }
    }
}
```
