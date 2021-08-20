#[cfg(feature = "allocator_api")]
pub use core::alloc::{AllocError, Allocator};

#[cfg(not(feature = "allocator_api"))]
use core::{
    alloc::Layout,
    fmt::{self, Display},
    ptr::NonNull,
};

#[cfg(all(feature = "allocator_api", feature = "alloc"))]
pub use alloc::alloc::Global;

/// Same as [`core::alloc::AllocError`], but stable.
/// When nightly feature is enabled, this is re-export of [`core::alloc::AllocError`] instead.
#[cfg(not(feature = "allocator_api"))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AllocError;

#[cfg(not(feature = "allocator_api"))]
impl Display for AllocError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("memory allocation failed")
    }
}

/// Same as [`core::alloc::Allocator`], but stable.
/// When nightly feature is enabled, this is re-export of [`core::alloc::Allocator`] instead.
#[cfg(not(feature = "allocator_api"))]
pub unsafe trait Allocator {
    /// See [`core::alloc::Allocator::allocate`].
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError>;

    /// See [`core::alloc::Allocator::deallocate`].
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout);
}

#[cfg(not(feature = "allocator_api"))]
unsafe impl<A> Allocator for &'_ A
where
    A: Allocator,
{
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        A::allocate(*self, layout)
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        A::deallocate(*self, ptr, layout)
    }
}

/// Same as [`alloc::alloc::Global`], but stable.
/// When nightly feature is enabled, this is re-export of [`alloc::alloc::Global`] instead.
#[cfg(all(not(feature = "allocator_api"), feature = "alloc"))]
#[derive(Clone, Copy, Debug, Default)]
pub struct Global;

#[cfg(all(not(feature = "allocator_api"), feature = "alloc"))]
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
