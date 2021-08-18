#[cfg(feature = "nightly")]
pub use core::alloc::{AllocError, Allocator};

#[cfg(not(feature = "nightly"))]
use core::{
    alloc::Layout,
    fmt::{self, Display},
    ptr::NonNull,
};

#[cfg(all(feature = "nightly", feature = "alloc"))]
pub use alloc::alloc::Global;

/// Same as [`core::alloc::AllocError`], but stable.
/// When nightly feature is enabled, this is re-export of [`core::alloc::AllocError`] instead.
#[cfg(not(feature = "nightly"))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AllocError;

#[cfg(not(feature = "nightly"))]
impl Display for AllocError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("memory allocation failed")
    }
}

/// Same as [`core::alloc::Allocator`], but stable.
/// When nightly feature is enabled, this is re-export of [`core::alloc::Allocator`] instead.
#[cfg(not(feature = "nightly"))]
pub unsafe trait Allocator {
    /// See [`core::alloc::Allocator::allocate`].
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError>;

    /// See [`core::alloc::Allocator::deallocate`].
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout);
}

/// Same as [`alloc::alloc::Global`], but stable.
/// When nightly feature is enabled, this is re-export of [`alloc::alloc::Global`] instead.
#[cfg(all(not(feature = "nightly"), feature = "alloc"))]
pub struct Global;

#[cfg(all(not(feature = "nightly"), feature = "alloc"))]
unsafe impl Allocator for Global {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        if layout.size() == 0 {
            Ok(NonNull::from(&mut []))
        } else {
            let ptr = unsafe { alloc::alloc::alloc(layout) };
            if ptr.is_null() {
                Err(AllocError)
            } else {
                Ok(unsafe {
                    NonNull::new_unchecked(core::slice::from_raw_parts_mut(ptr, layout.size()))
                })
            }
        }
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        alloc::alloc::dealloc(ptr.as_ptr(), layout)
    }
}
