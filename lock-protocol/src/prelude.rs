#[derive(Debug)]
pub enum Error {
    /// Invalid arguments provided.
    InvalidArgs,
    /// Insufficient memory available.
    NoMemory,
    /// Page fault occurred.
    PageFault,
    /// Access to a resource is denied.
    AccessDenied,
    /// Input/output error.
    IoError,
    /// Insufficient system resources.
    NotEnoughResources,
    /// Arithmetic Overflow occurred.
    Overflow,
    /// Memory mapping already exists for the given virtual address.
    MapAlreadyMappedVaddr,
    /// Error when allocating kernel virtual memory.
    KVirtAreaAllocError,
}

pub type Result<T> = core::result::Result<T, Error>;
