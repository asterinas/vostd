# Frame Lifecycle State Machine

Based on the Asterinas frame management codebase, here's how frames transition through different states with their corresponding transition functions.

## Frame States

### 1. **UNUSED** (REF_COUNT_UNUSED = u64::MAX)
- Frame is not in use and available for allocation
- Initial state for free physical memory pages
- Reference count set to maximum u64 value as an unused marker

### 2. **UNIQUE** (REF_COUNT_UNIQUE = u64::MAX - 1) 
- Frame is owned exclusively by a `UniqueFrame<M>`
- Cannot be shared or cloned
- Reference count set to u64::MAX - 1

### 3. **ACTIVE/IN-USE** (ref_count: 1..REF_COUNT_MAX)
- Frame is actively being used by one or more `Frame<M>` handles
- Reference counted, can be shared between multiple owners
- Reference count tracks number of handles

### 4. **RAW/FORGOTTEN** 
- Frame handle has been converted to a raw physical address
- Ownership temporarily transferred to external data structures (e.g., page tables)
- Can be restored later using `from_raw()`

## State Transition Functions

```mermaid
stateDiagram-v2
    [*] --> UNUSED : Physical memory initialization
    
    UNUSED --> UNIQUE : UniqueFrame::from_unused() + as_unique_ptr=true
    UNUSED --> ACTIVE : Frame::from_unused() + as_unique_ptr=false
    
    UNIQUE --> ACTIVE : UniqueFrame → Frame conversion
    
    ACTIVE --> RAW : Frame::into_raw()
    RAW --> ACTIVE : Frame::from_raw()
    
    ACTIVE --> ACTIVE : Frame::clone() [ref_count++]
    ACTIVE --> UNUSED : Frame::drop() [ref_count-- → 0]
    
    UNIQUE --> UNUSED : UniqueFrame::drop() [direct deallocation]
    
    state ACTIVE {
        [*] --> RefCount1
        RefCount1 --> RefCountN : clone()
        RefCountN --> RefCount1 : drop()
        RefCountN --> RefCountN : clone()/drop()
    }
```

## Detailed Transition Functions

### 1. `from_unused()` - UNUSED → ACTIVE/UNIQUE
```rust
// Located in: ostd/src/mm/frame/meta.rs
pub fn get_from_unused<M: AnyFrameMeta>(
    paddr: Paddr, 
    metadata: M, 
    as_unique_ptr: bool
) -> Result<PPtr<Self>, GetFrameError>
```
- **Preconditions**: Frame must have `REF_COUNT_UNUSED`
- **Actions**: 
  - Compare-and-exchange ref_count from `REF_COUNT_UNUSED` to `0`
  - Initialize metadata
  - Set ref_count to `REF_COUNT_UNIQUE` or `1` based on `as_unique_ptr`
- **Postconditions**: Frame moves to UNIQUE or ACTIVE state

### 2. `into_raw()` - ACTIVE → RAW
```rust
// Located in: ostd/src/mm/frame/mod.rs
pub fn into_raw(self) -> Paddr
```
- **Purpose**: Transfer ownership to external structures (e.g., page tables)
- **Actions**: 
  - Extract physical address
  - Forget the frame handle (using ManuallyDrop)
  - Move ownership tracking to `dropped_slots`
- **Result**: Returns raw physical address for external storage

### 3. `from_raw()` - RAW → ACTIVE  
```rust
// Located in: ostd/src/mm/frame/mod.rs
pub unsafe fn from_raw(paddr: Paddr) -> Self
```
- **Purpose**: Restore frame handle from raw physical address
- **Safety**: Must be previously forgotten frame via `into_raw()`
- **Actions**:
  - Create new frame handle from address
  - Restore ownership tracking from `dropped_slots`

### 4. `clone()` - ACTIVE → ACTIVE (reference counting)
```rust
impl<M: AnyFrameMeta + ?Sized> Clone for Frame<M> {
    fn clone(&self) -> Self {
        unsafe { self.slot().inc_ref_count() };
        // Create new handle with same pointer
    }
}
```
- **Actions**: Increment reference count, create new handle
- **Result**: Multiple handles to same physical frame

### 5. `drop()` - ACTIVE → UNUSED (when ref_count reaches 0)
```rust
impl<M: AnyFrameMeta + ?Sized> Drop for Frame<M> {
    fn drop(&mut self) {
        let last_ref_cnt = self.slot().ref_count.fetch_sub(1, Ordering::Release);
        if last_ref_cnt == 1 {
            // Last reference - deallocate frame
            unsafe { self.slot().drop_last_in_place() };
            // Set ref_count back to REF_COUNT_UNUSED
        }
    }
}
```

## Reference Count Values

| Value | State | Description |
|-------|-------|-------------|
| `u64::MAX` | UNUSED | Frame available for allocation |
| `u64::MAX - 1` | UNIQUE | Exclusively owned by UniqueFrame |
| `0` | TRANSITIONAL | Being constructed/destructed |
| `1..REF_COUNT_MAX` | ACTIVE | In use, ref-counted |
| `REF_COUNT_MAX..REF_COUNT_UNIQUE` | ILLEGAL | Overflow prevention range |

## Memory Safety Guarantees

1. **Type Safety**: Each frame has typed metadata `M: AnyFrameMeta`
2. **Reference Counting**: Prevents use-after-free via atomic reference counting
3. **Exclusive Access**: UniqueFrame provides exclusive ownership
4. **Raw Conversion Safety**: `into_raw()`/`from_raw()` pairs prevent double-free
5. **State Validation**: Atomic operations ensure consistent state transitions

## Usage in Page Tables

The `into_raw()`/`from_raw()` mechanism is specifically designed for page table integration:

```rust
// In page table code (ostd/src/mm/vm_space.rs)
unsafe impl PageTableConfig for UserPtConfig {
    fn item_into_raw(item: Self::Item) -> (Paddr, PagingLevel, PageProperty) {
        let (frame, prop) = item;
        let paddr = frame.into_raw(); // ACTIVE → RAW
        (paddr, level, prop)
    }
    
    unsafe fn item_from_raw(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> Self::Item {
        let frame = unsafe { Frame::from_raw(paddr) }; // RAW → ACTIVE
        (frame, prop)
    }
}
```

This allows page tables to store raw addresses while maintaining frame ownership semantics.
