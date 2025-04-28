use vstd::prelude::*;
use vstd::simple_pptr::*;

pub use crate::error::*;
pub use crate::pod::*;

verus! {

global layout usize is size == 8;

pub type Vaddr = usize;
pub const KERNEL_BASE_VADDR: Vaddr = 0xffff_8000_0000_0000;
pub const KERNEL_END_VADDR: Vaddr = 0xffff_ffff_ffff_0000;

pub const PAGE_SIZE: Vaddr = 4096;
pub const MAX_USERSPACE_VADDR: Vaddr = 0x0000_8000_0000_0000 - PAGE_SIZE;

pub struct Fallible;
pub struct Infallible;

}

verus! {

pub open spec fn pnt_add_spec(pnt: usize, len: usize) -> int {
    pnt + len
}

#[verifier::external_body]
pub fn pnt_add(pnt: *const u8, len: usize) -> (new_pnt: *const u8)
    ensures
        new_pnt as usize == pnt_add_spec(pnt as usize, len),
{
    (pnt as usize + len) as *const u8
}

pub open spec fn pnt_sub_spec(pnt: usize, len: usize) -> int {
    pnt - len
}

#[verifier::external_body]
pub fn pnt_sub(pnt: *const u8, len: usize) -> (new_pnt: *const u8)
    ensures
        new_pnt as usize == pnt_sub_spec(pnt as usize, len),
{
    (pnt as usize - len) as *const u8
}

pub open spec fn mut_pnt_add_spec(pnt: usize, len: usize) -> int {
    pnt + len
}

#[verifier::external_body]
pub fn mut_pnt_add(pnt: *mut u8, len: usize) -> (new_pnt: *mut u8)
    ensures
        new_pnt as usize == mut_pnt_add_spec(pnt as usize, len),
{
    (pnt as usize + len) as *mut u8
}

pub open spec fn mut_pnt_sub_spec(pnt: usize, len: usize) -> int {
    pnt - len
}

#[verifier::external_body]
pub fn mut_pnt_sub(pnt: *mut u8, len: usize) -> (new_pnt: *mut u8)
    ensures
        new_pnt as usize == mut_pnt_sub_spec(pnt as usize, len),
{
    (pnt as usize - len) as *mut u8
}

#[verifier::external_body]
pub fn vec_to_ptr(vec: &mut Vec<u8>) -> *mut u8 {
    unsafe{ vec as *mut Vec<u8> as *mut u8 }
}

#[verifier::external_body]
pub fn allocate_vec_zero(len: usize) -> (vec: Vec<u8>)
    ensures
        vec.len() == len,
{
    vec![0; len]
}

}

verus! {

pub open spec fn range_within_kspace_spec(start: usize, len: usize) -> bool {
    KERNEL_BASE_VADDR <= start && start + len <= KERNEL_END_VADDR
}

pub open spec fn range_within_uspace_spec(start: usize, len: usize) -> bool {
    0 <= start && start + len <= MAX_USERSPACE_VADDR
}

}

verus! {

extern "C" {
    /// Copies `size` bytes from `src` to `dst`. This function works with exception handling
    /// and can recover from page fault.
    /// Returns number of bytes that failed to copy.
    pub(crate) fn __memcpy_fallible(dst: *mut u8, src: *const u8, size: usize) -> usize;
    /// Fills `size` bytes in the memory pointed to by `dst` with the value `value`.
    /// This function works with exception handling and can recover from page fault.
    /// Returns number of bytes that failed to set.
    pub(crate) fn __memset_fallible(dst: *mut u8, value: u8, size: usize) -> usize;
}

#[verifier::external_body]
pub(crate) unsafe fn memcpy(dst: *mut u8, src: *const u8, len: usize) {
    // This method is implemented by calling `volatile_copy_memory`. Note that even with the
    // "volatile" keyword, data races are still considered undefined behavior (UB) in both the Rust
    // documentation and the C/C++ standards. In general, UB makes the behavior of the entire
    // program unpredictable, usually due to compiler optimizations that assume the absence of UB.
    // However, in this particular case, considering that the Linux kernel uses the "volatile"
    // keyword to implement `READ_ONCE` and `WRITE_ONCE`, the compiler is extremely unlikely to
    // break our code unless it also breaks the Linux kernel.
    //
    // For more details and future possibilities, see
    // <https://github.com/asterinas/asterinas/pull/1001#discussion_r1667317406>.

    // core::intrinsics::volatile_copy_memory(dst, src, len);
    core::ptr::copy(src, dst, len);
}

/// Copies `len` bytes from `src` to `dst`.
/// This function will early stop copying if encountering an unresolvable page fault.
///
/// Returns the number of successfully copied bytes.
///
/// In the following cases, this method may cause unexpected bytes to be copied, but will not cause
/// safety problems as long as the safety requirements are met:
/// - The source and destination overlap.
/// - The current context is not associated with valid user space (e.g., in the kernel thread).
///
/// # Safety
///
/// - `src` must either be [valid] for reads of `len` bytes or be in user space for `len` bytes.
/// - `dst` must either be [valid] for writes of `len` bytes or be in user space for `len` bytes.
///
/// [valid]: crate::mm::io#safety
#[verifier::external_body]
pub(crate) unsafe fn memcpy_fallible(dst: *mut u8, src: *const u8, len: usize) -> (copied_size: usize)
    ensures
        copied_size <= len,
{
    let failed_bytes = __memcpy_fallible(dst, src, len);
    len - failed_bytes
}

/// Fills `len` bytes of memory at `dst` with the specified `value`.
/// This function will early stop filling if encountering an unresolvable page fault.
///
/// Returns the number of successfully set bytes.
///
/// # Safety
///
/// - `dst` must either be [valid] for writes of `len` bytes or be in user space for `len` bytes.
///
/// [valid]: crate::mm::io#safety
#[verifier::external_body]
pub(crate) unsafe fn memset_fallible(dst: *mut u8, value: u8, len: usize) -> (set_size: usize)
    ensures
        set_size <= len,
{
    let failed_bytes = __memset_fallible(dst, value, len);
    len - failed_bytes
}

}

verus! {

/// A marker trait for POD types that can be read or written with one instruction.
///
/// We currently rely on this trait to ensure that the memory operation created by
/// `ptr::read_volatile` and `ptr::write_volatile` doesn't tear. However, the Rust documentation
/// makes no such guarantee, and even the wording in the LLVM LangRef is ambiguous.
///
/// At this point, we can only _hope_ that this doesn't break in future versions of the Rust or
/// LLVM compilers. However, this is unlikely to happen in practice, since the Linux kernel also
/// uses "volatile" semantics to implement `READ_ONCE`/`WRITE_ONCE`.
pub trait PodOnce: Pod {}

}
