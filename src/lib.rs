//!
//! Scoped-Arena provides arena allocator with explicit scopes.
//!
//! ## Arena allocation
//!
//! Arena allocators are simple and provides ludicrously fast allocation.\
//! Basically allocation requires only increment of internal pointer in the memory block to alignment of allocated object and then to size of allocated object and that's it.\
//! When memory block is exhausted arena will allocate new bigger memory block.\
//! Then arena can be reset after all allocated objects are not used anymore, keeping only last memory block and reuse it.\
//! After several warmup iterations the only memory block is large enough to handle all allocations until next reset.
//!
//!
//! ### Example
//!
//! ```rust
//! use scoped_arena::Scope;
//!
//! struct Cat {
//!     name: String,
//!     hungry: bool,
//! }
//!
//! /// Create new arena with `Global` allocator.
//! let mut scope = Scope::new();
//!
//! /// Construct a cat and move it to the scope.
//! let cat: &mut Cat = scope.to_scope(Cat {
//!     name: "Fluffy".to_owned(),
//!     hungry: true,
//! });
//!
//! // Now `cat` is a mutable reference bound to scope borrow lifetime.
//!
//! assert_eq!(&cat.name, "Fluffy");
//! assert!(cat.hungry);
//!
//! cat.hungry = false;
//!
//! // This cat instance on scope will be automatically dropped when `scope` is dropped or reset.
//! // It is impossible to reset before last usage of `cat`.
//!
//! // Next line will drop cat value and free memory occupied by it.
//! scope.reset();
//!
//! // If there were more cats or any other objects put on scope they all would be dropped and memory freed.
//! ```
//!
//! ## Scopes
//!
//! To reuse memory earlier this crates provides `Scope` with methods to create sub-`Scope`s.\
//! When sub-`Scope` is reset or dropped it will `Drop` all stored values and free memory allocated by the scope and flush last of new allocated memory block into parent.\
//! While objects allocated with parent `Scope` are unchanged and still valid.
//!
//! Well placed scopes can significantly reduce memory consumption.\
//! For example if few function calls use a lot of dynamic memory but don't need it to be available in caller\
//! they can be provided with sub-scope.\
//! At the same time any memory allocated in parent scope stays allocated.
//!
//! Creating sub-scope is cheap and allocating within sub-scope is as fast as allocating in parent scope.\
//!
//! ### Example
//!
//! ```rust
//! use scoped_arena::{Scope, ScopeProxy};
//!
//!
//! fn heavy_on_memory(mut scope: Scope<'_>, foobar: &String) {
//!     for _ in 0 .. 42 {
//!         let foobar: &mut String = scope.to_scope(foobar.clone());
//!     }
//!
//!     // new `scope` is dropped here and drops all allocated strings and frees memory.
//! }
//!
//! let mut scope = Scope::new();
//!
//! // Proxy is required to be friends with borrow checker.
//! // Creating sub-scope must lock parent `Scope` from being used, which requires mutable borrow, but any allocation borrows `Scope`.
//! // `Proxy` relaxes this a bit. `Proxy` borrows `Scope` mutably and tie allocated objects lifetime to scopes' borrow lifetime.
//! // So sub-scope can borrow proxy mutably while there are objects allocated from it.
//! let mut proxy = scope.proxy();
//!
//! let foobar: &mut String = proxy.to_scope("foobar".to_owned());
//!
//! // Make sub-scope for the call.
//! heavy_on_memory(proxy.scope(), &*foobar);
//!
//! // If `heavy_on_memory` didn't trigger new memory object allocation in the scope,
//! // sub-scope drop would rewind scope's internals to exactly the same state.
//! // Otherwise last of new blocks will become current block in parent scope.
//! //
//! // Note that `foobar` is still alive.
//!
//! heavy_on_memory(proxy.scope(), &*foobar);
//! heavy_on_memory(proxy.scope(), &*foobar);
//! heavy_on_memory(proxy.scope(), &*foobar);
//! heavy_on_memory(proxy.scope(), &*foobar);
//!
//! // Once peak memory consumption is reached, any number of `heavy_on_memory` calls would not require new memory blocks to be allocated.
//! // Even `loop { heavy_on_memory(proxy.scope(), &*foobar) }` will settle on some big enough block.
//! ```
//!
//! ## Dropping
//!
//! `to_scope` and `try_to_scope` methods store drop-glue for values that `needs_drop`.
//! On reset or drop scope iterates and properly drops all values.
//! No drop-glue is added for types that doesn't need drop. `Scope` allocates enough memory and writes value there, no bookkeeping overhead.
//!
//! ## Iterator collecting
//!
//! `to_scope_from_iter` method acts as `to_scope` but works on iterators and returns slices.
//! The limitation is that `to_scope_from_iter` need to allocate memory enough for upper bound of what iterator can yield.
//! If upper bound is too large or iterator is unbounded it will always fail.
//! One can use `try_to_scope_from_iter` so fail is `Err` and not panic.
//! It is safe for iterator to yield more items then upper bound it reports, `to_scope_from_iter` would not iterate past upper bound.
//! On success it returns mutable reference to slice with items from iterator in order.
//! All values will be dropped on scope reset or drop, same as with `to_scope`.
//!
//! This method is especially useful to deal with API that requires slices (*glares at FFI*), collecting into temporary `Vec` would cost much more.
//!

#![no_std]
#![cfg(any(feature = "allocator_api", feature = "alloc"))]
#![cfg_attr(feature = "allocator_api", feature(allocator_api))]

#[cfg(feature = "alloc")]
extern crate alloc;

mod allocator_api;
mod bucket;
mod drop;

use core::{
    alloc::Layout,
    fmt::{self, Debug},
    iter::IntoIterator,
    mem::{align_of, needs_drop, MaybeUninit},
    ptr::{self, write, NonNull},
    slice,
};

#[cfg(all(not(no_global_oom_handling), feature = "alloc"))]
use alloc::alloc::handle_alloc_error;

use self::{
    bucket::Buckets,
    drop::{DropList, WithDrop},
};

use self::allocator_api::{AllocError, Allocator};

#[cfg(feature = "alloc")]
use self::allocator_api::Global;

/// Scope associated with `Scope` allocator.
/// Allows placing values on the scope returning reference bound to scope borrow.
/// On drop scope drops all values placed onto it.
/// On drop scope frees all memory allocated from it.
#[cfg(not(feature = "alloc"))]
pub struct Scope<'arena, A: Allocator> {
    buckets: Buckets<'arena>,
    alloc: &'arena A,
    drop_list: DropList<'static>,
}

/// Scope associated with `Scope` allocator.
/// Allows placing values on the scope returning reference bound to scope borrow.
/// On drop scope drops all values placed onto it.
/// On drop scope frees all memory allocated from it.
#[cfg(feature = "alloc")]
pub struct Scope<'arena, A: Allocator = Global> {
    buckets: Buckets<'arena>,
    alloc: A,
    drop_list: DropList<'static>,
}

impl<A> Debug for Scope<'_, A>
where
    A: Allocator,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Scope")
            .field("buckets", &self.buckets)
            .finish_non_exhaustive()
    }
}

impl<A> Drop for Scope<'_, A>
where
    A: Allocator,
{
    #[inline(always)]
    fn drop(&mut self) {
        unsafe {
            self.drop_list.reset();
            self.buckets.reset(&self.alloc, false);
        }
    }
}

#[cfg(feature = "alloc")]
impl Scope<'_, Global> {
    /// Returns new instance of arena allocator based on [`Global`] allocator.
    #[inline(always)]
    pub fn new() -> Self {
        Scope::new_in(Global)
    }

    /// Returns new instance of arena allocator based on [`Global`] allocator
    /// with preallocated capacity in bytes.
    #[inline(always)]
    pub fn with_capacity(capacity: usize) -> Self {
        Scope::with_capacity_in(capacity, Global)
    }
}

impl<A> Scope<'_, A>
where
    A: Allocator,
{
    /// Returns new instance of arena allocator based on provided allocator.
    #[inline(always)]
    pub fn new_in(alloc: A) -> Self {
        Scope::with_capacity_in(0, alloc)
    }

    /// Returns new instance of arena allocator based on provided allocator
    /// with preallocated capacity in bytes.
    #[inline(always)]
    pub fn with_capacity_in(capacity: usize, alloc: A) -> Self {
        Scope {
            buckets: Buckets::new(capacity, &alloc).expect(ALLOCATOR_CAPACITY_OVERFLOW),
            alloc,
            drop_list: DropList::new(),
        }
    }
}

impl<A> Scope<'_, A>
where
    A: Allocator,
{
    #[inline(always)]
    pub fn reset(&mut self) {
        unsafe {
            self.drop_list.reset();
            self.buckets.reset(&self.alloc, true);
        }
    }

    /// Allocates a block of memory.
    /// Returns a [`&mut [MaybeUninit<u8>]`] meeting the size and alignment guarantees of layout.
    /// Actual size of the returned size MAY be larger than requested.
    /// The returned block should be initialized before use.
    ///
    /// Returned block will be deallocated when scope is dropped.
    #[cfg(all(not(no_global_oom_handling), feature = "alloc"))]
    #[inline(always)]
    pub fn alloc(&self, layout: Layout) -> &mut [MaybeUninit<u8>] {
        match self.try_alloc(layout) {
            Ok(buf) => buf,
            Err(_) => handle_alloc_error(layout),
        }
    }

    /// Attempts to allocate a block of memory.
    /// On success, returns a [`&mut [MaybeUninit<u8>]`] meeting the size and alignment guarantees of layout.
    /// Actual size of the returned size MAY be larger than requested.
    /// The returned block should be initialized before use.
    ///
    /// Returned block will be deallocated when scope is dropped.
    ///
    /// # Errors
    ///
    /// Returning `Err` indicates that memory is exhausted.
    #[inline(always)]
    pub fn try_alloc(&self, layout: Layout) -> Result<&mut [MaybeUninit<u8>], AllocError> {
        unsafe { self.buckets.allocate(layout, &self.alloc) }
    }

    /// Allocates a block of memory.
    /// Returns a [`&mut [u8]`] meeting the size and alignment guarantees of layout.
    /// Actual size of the returned size MAY be larger than requested.
    /// The returned block contents is zero-initialized.
    ///
    /// Returned block will be deallocated when scope is dropped.
    #[cfg(all(not(no_global_oom_handling), feature = "alloc"))]
    #[inline(always)]
    pub fn alloc_zeroed(&self, layout: Layout) -> &mut [u8] {
        match self.try_alloc_zeroed(layout) {
            Ok(buf) => buf,
            Err(_) => handle_alloc_error(layout),
        }
    }

    /// Attempts to allocate a block of memory.
    /// On success, returns a [`&mut [u8]`] meeting the size and alignment guarantees of layout.
    /// Actual size of the returned size MAY be larger than requested.
    /// The returned block contents is zero-initialized.
    ///
    /// Returned block will be deallocated when scope is dropped.
    ///
    /// # Errors
    ///
    /// Returning `Err` indicates that memory is exhausted.
    #[inline(always)]
    pub fn try_alloc_zeroed(&self, layout: Layout) -> Result<&mut [u8], AllocError> {
        let buf = unsafe { self.buckets.allocate(layout, &self.alloc) }?;

        let buf = unsafe {
            // Zeroing bytes buffer should be safe.
            ptr::write_bytes(buf.as_mut_ptr(), 0, buf.len());

            // Zero-initialized.
            slice::from_raw_parts_mut(buf.as_mut_ptr() as *mut u8, buf.len())
        };

        Ok(buf)
    }

    /// Move value onto the scope.
    /// Returns mutable reference to value with lifetime equal to scope borrow lifetime.
    /// Value on scope will be dropped when scope is dropped.
    ///
    /// This method is as cheap as allocation if value does not needs dropping as reported by [`core::mem::needs_drop`].
    #[cfg(all(not(no_global_oom_handling), feature = "alloc"))]
    #[inline(always)]
    pub fn to_scope<T>(&self, value: T) -> &mut T {
        self.to_scope_with(|| value)
    }

    /// Places value returned from function onto the scope.
    /// Returns mutable reference to value with lifetime equal to scope borrow lifetime.
    /// Value on scope will be dropped when scope is dropped.
    ///
    /// This method is as cheap as allocation if value does not needs dropping as reported by [`core::mem::needs_drop`].
    #[cfg(all(not(no_global_oom_handling), feature = "alloc"))]
    #[inline(always)]
    pub fn to_scope_with<F, T>(&self, f: F) -> &mut T
    where
        F: FnOnce() -> T,
    {
        match self.try_to_scope_with(f) {
            Ok(value) => value,
            Err(_) => handle_alloc_error(Layout::new::<T>()),
        }
    }

    /// Tries to move value onto the scope.
    /// On success, returns mutable reference to value with lifetime equal to scope borrow lifetime.
    /// Value on scope will be dropped when scope is dropped.
    ///
    /// This method is as cheap as allocation if value does not needs dropping as reported by [`core::mem::needs_drop`].
    ///
    /// # Errors
    ///
    /// Returning `Err` indicates that memory is exhausted.
    /// Returning `Err` contains original value.
    #[inline(always)]
    pub fn try_to_scope<T>(&self, value: T) -> Result<&mut T, (AllocError, T)> {
        self.try_to_scope_with(|| value)
            .map_err(|(err, f)| (err, f()))
    }

    /// Tries to place value return from function onto the scope.
    /// On success, returns mutable reference to value with lifetime equal to scope borrow lifetime.
    /// Value on scope will be dropped when scope is dropped.
    ///
    /// This method is as cheap as allocation if value does not needs dropping as reported by [`core::mem::needs_drop`].
    ///
    /// # Errors
    ///
    /// Returning `Err` indicates that memory is exhausted.
    /// Returning `Err` contains original value.
    #[inline(always)]
    pub fn try_to_scope_with<F, T>(&self, f: F) -> Result<&mut T, (AllocError, F)>
    where
        F: FnOnce() -> T,
    {
        try_to_scope_with(|layout| self.try_alloc(layout), &self.drop_list, f)
    }

    /// Move values from iterator onto the scope.
    /// Returns mutable reference to slice with lifetime equal to scope borrow lifetime.
    /// Values on scope will be dropped when scope is dropped.
    ///
    /// This method is as cheap as allocation if value does not needs dropping as reported by [`core::mem::needs_drop`].
    ///
    /// This method allocates memory to hold iterator's upper bound number of items. See [`core::iter::Iterator::size_hint`].
    /// It will not consume more items.
    /// This method will always fail for unbound iterators.
    #[cfg(all(not(no_global_oom_handling), feature = "alloc"))]
    #[inline(always)]
    pub fn to_scope_from_iter<T, I>(&self, iter: I) -> &mut [T]
    where
        I: IntoIterator<Item = T>,
    {
        let too_large_layout = unsafe {
            Layout::from_size_align_unchecked(usize::MAX - align_of::<T>(), align_of::<T>())
        };
        let iter = iter.into_iter();
        let upper_bound = iter
            .size_hint()
            .1
            .unwrap_or_else(|| handle_alloc_error(too_large_layout));

        match self.try_to_scope_from_iter(iter) {
            Ok(slice) => slice,
            Err(_) => {
                handle_alloc_error(Layout::array::<T>(upper_bound).unwrap_or(too_large_layout))
            }
        }
    }

    /// Tries to move values from iterator onto the scope.
    /// On success, returns mutable reference to slice with lifetime equal to scope borrow lifetime.
    /// Values on scope will be dropped when scope is dropped.
    ///
    /// This method is as cheap as allocation if value does not needs dropping as reported by [`core::mem::needs_drop`].
    ///
    /// This method allocates memory to hold iterator's upper bound number of items. See [`core::iter::Iterator::size_hint`].
    /// It will not consume more items.
    /// This method will always fail for unbound iterators.
    ///
    /// # Errors
    ///
    /// Returning `Err` indicates that memory is exhausted.
    /// Returning `Err` contains original iterator.
    #[inline(always)]
    pub fn try_to_scope_from_iter<T, I>(
        &self,
        iter: I,
    ) -> Result<&mut [T], (AllocError, I::IntoIter)>
    where
        I: IntoIterator<Item = T>,
    {
        try_to_scope_from_iter(|layout| self.try_alloc(layout), &self.drop_list, iter)
    }

    /// Put multiple clones of the value onto the scope.
    /// Returns mutable reference to slice with lifetime equal to scope borrow lifetime.
    /// Values on scope will be dropped when scope is dropped.
    ///
    /// This method is as cheap as allocation if value does not needs dropping as reported by [`core::mem::needs_drop`].
    #[inline(always)]
    pub fn to_scope_many<T>(&self, count: usize, value: T) -> &mut [T]
    where
        T: Clone,
    {
        let too_large_layout = unsafe {
            Layout::from_size_align_unchecked(usize::MAX - align_of::<T>(), align_of::<T>())
        };
        match self.try_to_scope_many(count, value) {
            Ok(slice) => slice,
            Err(_) => handle_alloc_error(Layout::array::<T>(count).unwrap_or(too_large_layout)),
        }
    }

    /// Tries to put multiple clones of the value onto the scope.
    /// On success, returns mutable reference to slice with lifetime equal to scope borrow lifetime.
    /// Returns mutable reference to slice with lifetime equal to scope borrow lifetime.
    /// Values on scope will be dropped when scope is dropped.
    ///
    /// This method is as cheap as allocation if value does not needs dropping as reported by [`core::mem::needs_drop`].
    #[inline(always)]
    pub fn try_to_scope_many<T>(&self, count: usize, value: T) -> Result<&mut [T], AllocError>
    where
        T: Clone,
    {
        self.try_to_scope_many_with(count, || value.clone())
    }

    /// Put multiple values created by calls to the specified function onto the scope.
    /// Returns mutable reference to slice with lifetime equal to scope borrow lifetime.
    /// Values on scope will be dropped when scope is dropped.
    ///
    /// This method is as cheap as allocation if value does not needs dropping as reported by [`core::mem::needs_drop`].
    #[inline(always)]
    pub fn to_scope_many_with<T, F>(&self, count: usize, f: F) -> &mut [T]
    where
        F: FnMut() -> T,
    {
        let too_large_layout = unsafe {
            Layout::from_size_align_unchecked(usize::MAX - align_of::<T>(), align_of::<T>())
        };
        match self.try_to_scope_many_with(count, f) {
            Ok(slice) => slice,
            Err(_) => handle_alloc_error(Layout::array::<T>(count).unwrap_or(too_large_layout)),
        }
    }

    /// Tries to put multiple values created by calls to the specified function onto the scope.
    /// On success, returns mutable reference to slice with lifetime equal to scope borrow lifetime.
    /// Returns mutable reference to slice with lifetime equal to scope borrow lifetime.
    /// Values on scope will be dropped when scope is dropped.
    ///
    /// This method is as cheap as allocation if value does not needs dropping as reported by [`core::mem::needs_drop`].
    #[inline(always)]
    pub fn try_to_scope_many_with<T, F>(&self, count: usize, f: F) -> Result<&mut [T], AllocError>
    where
        F: FnMut() -> T,
    {
        try_to_scope_many_with(|layout| self.try_alloc(layout), &self.drop_list, count, f)
    }

    /// Reports total memory allocated from underlying allocator by associated arena.
    #[inline(always)]
    pub fn total_memory_usage(&self) -> usize {
        self.buckets.total_memory_usage()
    }

    /// Creates scope proxy bound to the scope.
    /// Any objects allocated through proxy will be attached to the scope.
    /// Returned proxy will use reference to the underlying allocator.
    #[inline(always)]
    pub fn proxy_ref<'a>(&'a mut self) -> ScopeProxy<'a, &'a A> {
        ScopeProxy {
            buckets: self.buckets.fork(),
            alloc: &self.alloc,
            drop_list: self.drop_list.fork(),
        }
    }
}

impl<A> Scope<'_, A>
where
    A: Allocator + Clone,
{
    /// Creates scope proxy bound to the scope.
    /// Any objects allocated through proxy will be attached to the scope.
    /// Returned proxy will use clone of the underlying allocator.
    #[inline(always)]
    pub fn proxy<'a>(&'a mut self) -> ScopeProxy<'a, A> {
        ScopeProxy {
            buckets: self.buckets.fork(),
            alloc: self.alloc.clone(),
            drop_list: self.drop_list.fork(),
        }
    }
}

/// Proxy for `Scope` which allocates memory bound to the scope lifetime and not itself.
/// This allows to create sub-scopes while keeping references to scoped values.
/// Does not frees memory and does not drops values moved on scope when dropped.
/// Parent `Scope` will do this.
#[cfg(not(feature = "alloc"))]
pub struct ScopeProxy<'scope, A: Allocator> {
    buckets: Buckets<'scope>,
    alloc: &'scope A,
    drop_list: DropList<'scope>,
}

/// Proxy for `Scope` which allocates memory bound to the scope lifetime and not itself.
/// This allows to create sub-scopes while keeping references to scoped values.
/// Does not frees memory and does not drops values moved on scope when dropped.
/// Parent `Scope` will do this.
#[cfg(feature = "alloc")]
pub struct ScopeProxy<'scope, A: Allocator = Global> {
    buckets: Buckets<'scope>,
    alloc: A,
    drop_list: DropList<'scope>,
}

impl<A> Debug for ScopeProxy<'_, A>
where
    A: Allocator,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ScopeProxy")
            .field("buckets", &self.buckets)
            .finish_non_exhaustive()
    }
}

impl<A> Drop for ScopeProxy<'_, A>
where
    A: Allocator,
{
    #[inline(always)]
    fn drop(&mut self) {
        unsafe {
            self.drop_list.flush_fork();
            self.buckets.flush_fork();
        }
    }
}

impl<'scope, A> ScopeProxy<'scope, A>
where
    A: Allocator,
{
    /// Allocates a block of memory.
    /// Returns a [`&mut [MaybeUninit<u8>]`] meeting the size and alignment guarantees of layout.
    /// The returned block should be initialized before use.
    ///
    /// Returned block will be deallocated when scope is dropped.
    #[cfg(all(not(no_global_oom_handling), feature = "alloc"))]
    #[inline(always)]
    pub fn alloc(&self, layout: Layout) -> &'scope mut [MaybeUninit<u8>] {
        match self.try_alloc(layout) {
            Ok(buf) => buf,
            Err(_) => handle_alloc_error(layout),
        }
    }

    /// Attempts to allocate a block of memory.
    /// On success, returns a [`&mut [MaybeUninit<u8>]`] meeting the size and alignment guarantees of layout.
    /// The returned block should be initialized before use.
    ///
    /// Returned block will be deallocated when scope is dropped.
    ///
    /// # Errors
    ///
    /// Returning `Err` indicates that memory is exhausted.
    #[inline(always)]
    pub fn try_alloc(&self, layout: Layout) -> Result<&'scope mut [MaybeUninit<u8>], AllocError> {
        unsafe { self.buckets.allocate(layout, &self.alloc) }
    }

    /// Allocates a block of memory.
    /// Returns a [`&mut [u8]`] meeting the size and alignment guarantees of layout.
    /// The returned block contents is zero-initialized.
    ///
    /// Returned block will be deallocated when scope is dropped.
    #[cfg(all(not(no_global_oom_handling), feature = "alloc"))]
    #[inline(always)]
    pub fn alloc_zeroed(&self, layout: Layout) -> &mut [u8] {
        match self.try_alloc_zeroed(layout) {
            Ok(buf) => buf,
            Err(_) => handle_alloc_error(layout),
        }
    }

    /// Attempts to allocate a block of memory.
    /// On success, returns a [`&mut [u8]`] meeting the size and alignment guarantees of layout.
    /// The returned block contents is zero-initialized.
    ///
    /// Returned block will be deallocated when scope is dropped.
    ///
    /// # Errors
    ///
    /// Returning `Err` indicates that memory is exhausted.
    #[inline(always)]
    pub fn try_alloc_zeroed(&self, layout: Layout) -> Result<&mut [u8], AllocError> {
        let buf = unsafe { self.buckets.allocate(layout, &self.alloc) }?;

        let buf = unsafe {
            // Zeroing bytes buffer should be safe.
            ptr::write_bytes(buf.as_mut_ptr(), 0, buf.len());

            // Zero-initialized.
            slice::from_raw_parts_mut(buf.as_mut_ptr() as *mut u8, buf.len())
        };

        Ok(buf)
    }

    /// Move value onto the scope.
    /// Returns mutable reference to value with lifetime equal to 'scope lifetime.
    /// Value on scope will be dropped when scope is dropped.
    ///
    /// This method is as cheap as allocation if value does not needs dropping as reported by [`core::mem::needs_drop`].
    #[cfg(all(not(no_global_oom_handling), feature = "alloc"))]
    #[inline(always)]
    pub fn to_scope<T>(&self, value: T) -> &'scope mut T {
        self.to_scope_with(|| value)
    }

    /// Places value returned from function onto the scope.
    /// Returns mutable reference to value with lifetime equal to scope borrow lifetime.
    /// Value on scope will be dropped when scope is dropped.
    ///
    /// This method is as cheap as allocation if value does not needs dropping as reported by [`core::mem::needs_drop`].
    #[cfg(all(not(no_global_oom_handling), feature = "alloc"))]
    #[inline(always)]
    pub fn to_scope_with<F, T>(&self, f: F) -> &'scope mut T
    where
        F: FnOnce() -> T,
    {
        match self.try_to_scope_with(f) {
            Ok(value) => value,
            Err(_) => handle_alloc_error(Layout::new::<T>()),
        }
    }

    /// Tries to move value onto the scope.
    /// On success, returns mutable reference to value with lifetime to equal 'scope lifetime.
    /// Value on scope will be dropped when scope is dropped.
    ///
    /// This method is as cheap as allocation if value does not needs dropping as reported by [`core::mem::needs_drop`].
    ///
    /// # Errors
    ///
    /// Returning `Err` indicates that memory is exhausted.
    /// Returning `Err` contains original value.
    #[inline(always)]
    pub fn try_to_scope<T>(&self, value: T) -> Result<&'scope mut T, (AllocError, T)> {
        self.try_to_scope_with(|| value)
            .map_err(|(err, f)| (err, f()))
    }

    /// Tries to place value return from function onto the scope.
    /// On success, returns mutable reference to value with lifetime equal to scope borrow lifetime.
    /// Value on scope will be dropped when scope is dropped.
    ///
    /// This method is as cheap as allocation if value does not needs dropping as reported by [`core::mem::needs_drop`].
    ///
    /// # Errors
    ///
    /// Returning `Err` indicates that memory is exhausted.
    /// Returning `Err` contains original value.
    #[inline(always)]
    pub fn try_to_scope_with<F, T>(&self, f: F) -> Result<&'scope mut T, (AllocError, F)>
    where
        F: FnOnce() -> T,
    {
        try_to_scope_with(|layout| self.try_alloc(layout), &self.drop_list, f)
    }

    /// Move values from iterator onto the scope.
    /// Returns mutable reference to slice with lifetime equal to 'scope lifetime.
    /// Values on scope will be dropped when scope is dropped.
    ///
    /// This method is as cheap as allocation if value does not needs dropping as reported by [`core::mem::needs_drop`].
    ///
    /// This method allocates memory to hold iterator's upper bound number of items. See [`core::iter::Iterator::size_hint`].
    /// It will not consume more items.
    /// This method will always fail for unbound iterators.
    #[cfg(all(not(no_global_oom_handling), feature = "alloc"))]
    #[inline(always)]
    pub fn to_scope_from_iter<T, I>(&self, iter: I) -> &'scope mut [T]
    where
        I: IntoIterator<Item = T>,
    {
        let too_large_layout = unsafe {
            Layout::from_size_align_unchecked(usize::MAX - align_of::<T>(), align_of::<T>())
        };
        let iter = iter.into_iter();
        let upper_bound = iter
            .size_hint()
            .1
            .unwrap_or_else(|| handle_alloc_error(too_large_layout));

        match self.try_to_scope_from_iter(iter) {
            Ok(slice) => slice,
            Err(_) => {
                handle_alloc_error(Layout::array::<T>(upper_bound).unwrap_or(too_large_layout))
            }
        }
    }

    /// Tries to move values from iterator onto the scope.
    /// On success, returns mutable reference to slice with lifetime equal to 'scope lifetime.
    /// Values on scope will be dropped when scope is dropped.
    ///
    /// This method is as cheap as allocation if value does not needs dropping as reported by [`core::mem::needs_drop`].
    ///
    /// This method allocates memory to hold iterator's upper bound number of items. See [`core::iter::Iterator::size_hint`].
    /// It will not consume more items.
    /// This method will always fail for unbound iterators.
    ///
    /// # Errors
    ///
    /// Returning `Err` indicates that memory is exhausted.
    /// Returning `Err` contains original iterator.
    #[inline(always)]
    pub fn try_to_scope_from_iter<T, I>(
        &self,
        iter: I,
    ) -> Result<&'scope mut [T], (AllocError, I::IntoIter)>
    where
        I: IntoIterator<Item = T>,
    {
        try_to_scope_from_iter(|layout| self.try_alloc(layout), &self.drop_list, iter)
    }

    /// Put multiple clones of the value onto the scope.
    /// Returns mutable reference to slice with lifetime equal to scope borrow lifetime.
    /// Values on scope will be dropped when scope is dropped.
    ///
    /// This method is as cheap as allocation if value does not needs dropping as reported by [`core::mem::needs_drop`].
    #[inline(always)]
    pub fn to_scope_many<T>(&self, count: usize, value: T) -> &'scope mut [T]
    where
        T: Clone,
    {
        let too_large_layout = unsafe {
            Layout::from_size_align_unchecked(usize::MAX - align_of::<T>(), align_of::<T>())
        };
        match self.try_to_scope_many(count, value) {
            Ok(slice) => slice,
            Err(_) => handle_alloc_error(Layout::array::<T>(count).unwrap_or(too_large_layout)),
        }
    }

    /// Tries to put multiple clones of the value onto the scope.
    /// On success, returns mutable reference to slice with lifetime equal to scope borrow lifetime.
    /// Returns mutable reference to slice with lifetime equal to scope borrow lifetime.
    /// Values on scope will be dropped when scope is dropped.
    ///
    /// This method is as cheap as allocation if value does not needs dropping as reported by [`core::mem::needs_drop`].
    #[inline(always)]
    pub fn try_to_scope_many<T>(
        &self,
        count: usize,
        value: T,
    ) -> Result<&'scope mut [T], AllocError>
    where
        T: Clone,
    {
        self.try_to_scope_many_with(count, || value.clone())
    }

    /// Put multiple values created by calls to the specified function onto the scope.
    /// Returns mutable reference to slice with lifetime equal to scope borrow lifetime.
    /// Values on scope will be dropped when scope is dropped.
    ///
    /// This method is as cheap as allocation if value does not needs dropping as reported by [`core::mem::needs_drop`].
    #[inline(always)]
    pub fn to_scope_many_with<T, F>(&self, count: usize, f: F) -> &'scope mut [T]
    where
        F: FnMut() -> T,
    {
        let too_large_layout = unsafe {
            Layout::from_size_align_unchecked(usize::MAX - align_of::<T>(), align_of::<T>())
        };
        match self.try_to_scope_many_with(count, f) {
            Ok(slice) => slice,
            Err(_) => handle_alloc_error(Layout::array::<T>(count).unwrap_or(too_large_layout)),
        }
    }

    /// Tries to put multiple values created by calls to the specified function onto the scope.
    /// On success, returns mutable reference to slice with lifetime equal to scope borrow lifetime.
    /// Returns mutable reference to slice with lifetime equal to scope borrow lifetime.
    /// Values on scope will be dropped when scope is dropped.
    ///
    /// This method is as cheap as allocation if value does not needs dropping as reported by [`core::mem::needs_drop`].
    #[inline(always)]
    pub fn try_to_scope_many_with<T, F>(
        &self,
        count: usize,
        f: F,
    ) -> Result<&'scope mut [T], AllocError>
    where
        F: FnMut() -> T,
    {
        try_to_scope_many_with(|layout| self.try_alloc(layout), &self.drop_list, count, f)
    }

    /// Reports total memory allocated from underlying allocator by associated arena.
    #[inline(always)]
    pub fn total_memory_usage(&self) -> usize {
        self.buckets.total_memory_usage()
    }

    /// Creates new scope which inherits from the proxy's scope.
    /// This scope becomes locked until returned scope is dropped.
    /// Returned scope will use reference to the underlying allocator.
    #[inline(always)]
    pub fn scope_ref<'a>(&'a mut self) -> Scope<'a, &'a A> {
        Scope {
            buckets: self.buckets.fork(),
            alloc: &self.alloc,
            drop_list: DropList::new(),
        }
    }
}

impl<A> ScopeProxy<'_, A>
where
    A: Allocator + Clone,
{
    /// Creates new scope which inherits from the proxy's scope.
    /// This scope becomes locked until returned scope is dropped.
    /// Returned scope will use clone of the underlying allocator.
    #[inline(always)]
    pub fn scope<'a>(&'a mut self) -> Scope<'a, A> {
        Scope {
            buckets: self.buckets.fork(),
            alloc: self.alloc.clone(),
            drop_list: DropList::new(),
        }
    }
}

const ALLOCATOR_CAPACITY_OVERFLOW: &'static str = "Allocator capacity overflow";

unsafe impl<A> Allocator for &'_ Scope<'_, A>
where
    A: Allocator,
{
    #[inline(always)]
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        let buf = self.try_alloc(layout)?;
        let ptr = unsafe {
            NonNull::new_unchecked(core::ptr::slice_from_raw_parts_mut(
                buf.as_mut_ptr() as *mut u8,
                buf.len(),
            ))
        };
        Ok(ptr)
    }

    #[inline(always)]
    unsafe fn deallocate(&self, _ptr: NonNull<u8>, _layout: Layout) {
        // Will be deallocated on scope drop.
    }

    #[cfg(feature = "allocator_api")]
    #[inline(always)]
    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        debug_assert!(
            new_layout.size() <= old_layout.size(),
            "`new_layout.size()` must be smaller than or equal to `old_layout.size()`"
        );

        // Returns same memory unchanged.
        // This is valid behavior as change in layout won't affect deallocation
        // and for `grow{_zeroed}` methods new layout with smaller size will only affect numbers of bytes copied.
        Ok(NonNull::new_unchecked(core::slice::from_raw_parts_mut(
            ptr.as_ptr(),
            old_layout.size(),
        )))
    }
}

unsafe impl<A> Allocator for ScopeProxy<'_, A>
where
    A: Allocator,
{
    #[inline(always)]
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        let buf = self.try_alloc(layout)?;
        let ptr = unsafe {
            NonNull::new_unchecked(core::ptr::slice_from_raw_parts_mut(
                buf.as_mut_ptr() as *mut u8,
                buf.len(),
            ))
        };
        Ok(ptr)
    }

    #[inline(always)]
    unsafe fn deallocate(&self, _ptr: NonNull<u8>, _layout: Layout) {
        // Will be deallocated on scope drop.
    }

    #[cfg(feature = "allocator_api")]
    #[inline(always)]
    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        debug_assert!(
            new_layout.size() <= old_layout.size(),
            "`new_layout.size()` must be smaller than or equal to `old_layout.size()`"
        );

        // Returns same memory unchanged.
        // This is valid behavior as change in layout won't affect deallocation
        // and for `grow{_zeroed}` methods new layout with smaller size will only affect numbers of bytes copied.
        Ok(NonNull::new_unchecked(core::slice::from_raw_parts_mut(
            ptr.as_ptr(),
            old_layout.size(),
        )))
    }
}

#[inline(always)]
fn try_to_scope_with<'a, F, T>(
    try_alloc: impl FnOnce(Layout) -> Result<&'a mut [MaybeUninit<u8>], AllocError>,
    drop_list: &DropList,
    f: F,
) -> Result<&'a mut T, (AllocError, F)>
where
    F: FnOnce() -> T,
{
    if needs_drop::<T>() {
        match try_alloc(Layout::new::<WithDrop<T>>()) {
            Ok(buf) => {
                let value = unsafe { WithDrop::init(buf, f(), drop_list) };
                Ok(value)
            }
            Err(err) => Err((err, f)),
        }
    } else {
        match try_alloc(Layout::new::<T>()) {
            Ok(buf) => {
                let uninit = unsafe { cast_buf(buf) };
                unsafe { write(uninit.as_mut_ptr(), f()) };
                Ok(unsafe { uninit.assume_init_mut() })
            }
            Err(err) => Err((err, f)),
        }
    }
}

fn try_to_scope_from_iter<'a, T, I>(
    try_alloc: impl FnOnce(Layout) -> Result<&'a mut [MaybeUninit<u8>], AllocError>,
    drop_list: &DropList,
    iter: I,
) -> Result<&'a mut [T], (AllocError, I::IntoIter)>
where
    I: IntoIterator<Item = T>,
{
    let iter = iter.into_iter();
    let upper_bound = match iter.size_hint().1 {
        Some(upper_bound) => upper_bound,
        None => return Err((AllocError, iter)),
    };

    if needs_drop::<T>() {
        match WithDrop::<T>::array_layout(upper_bound) {
            Some(layout) => match try_alloc(layout) {
                Ok(buf) => {
                    let slice = unsafe { WithDrop::init_iter(buf, iter, drop_list) };
                    Ok(slice)
                }
                Err(err) => Err((err, iter)),
            },
            None => Err((AllocError, iter)),
        }
    } else {
        match Layout::array::<T>(upper_bound) {
            Ok(layout) => match try_alloc(layout) {
                Ok(buf) => {
                    let (uninit, _) = unsafe {
                        // Buffer with layout for `[T; upper_bound]` was requested.
                        cast_buf_array::<T>(buf)
                    };

                    let item_count = iter.take(uninit.len()).fold(0, |idx, item| {
                        uninit[idx].write(item);
                        idx + 1
                    });

                    let slice = unsafe {
                        // First `item_count` elements of the array were initialized from iterator
                        core::slice::from_raw_parts_mut(uninit.as_mut_ptr() as *mut T, item_count)
                    };
                    Ok(slice)
                }
                Err(err) => Err((err, iter)),
            },
            Err(_) => Err((AllocError, iter)),
        }
    }
}

fn try_to_scope_many_with<'a, T>(
    try_alloc: impl FnOnce(Layout) -> Result<&'a mut [MaybeUninit<u8>], AllocError>,
    drop_list: &DropList,
    count: usize,
    mut f: impl FnMut() -> T,
) -> Result<&'a mut [T], AllocError> {
    if needs_drop::<T>() {
        match WithDrop::<T>::array_layout(count) {
            Some(layout) => match try_alloc(layout) {
                Ok(buf) => {
                    let slice = unsafe { WithDrop::init_many(buf, count, f, drop_list) };
                    Ok(slice)
                }
                Err(err) => Err(err),
            },
            None => Err(AllocError),
        }
    } else {
        match Layout::array::<T>(count) {
            Ok(layout) => match try_alloc(layout) {
                Ok(buf) => {
                    let (uninit, _) = unsafe {
                        // Buffer with layout for `[T; upper_bound]` was requested.
                        cast_buf_array::<T>(buf)
                    };

                    for i in 0..count {
                        uninit[i].write(f());
                    }

                    let slice = unsafe {
                        // First `item_count` elements of the array were initialized from iterator
                        core::slice::from_raw_parts_mut(uninit.as_mut_ptr() as *mut T, count)
                    };
                    Ok(slice)
                }
                Err(err) => Err(err),
            },
            Err(_) => Err(AllocError),
        }
    }
}

unsafe fn cast_buf<T>(buf: &mut [MaybeUninit<u8>]) -> &mut MaybeUninit<T> {
    let layout = Layout::new::<T>();
    debug_assert_eq!(0, buf.as_mut_ptr() as usize % layout.align());
    debug_assert!(buf.len() >= layout.size());
    &mut *(buf.as_mut_ptr() as *mut MaybeUninit<T>)
}

unsafe fn cast_buf_array<T>(
    buf: &mut [MaybeUninit<u8>],
) -> (&mut [MaybeUninit<T>], &mut [MaybeUninit<u8>]) {
    let layout = Layout::new::<T>();
    debug_assert_eq!(0, buf.as_mut_ptr() as usize % layout.align());
    let len = buf.len() / layout.size();

    let (head, tail) = buf.split_at_mut(len * layout.size());
    let head = slice::from_raw_parts_mut(head.as_mut_ptr() as *mut MaybeUninit<T>, len);
    (head, tail)
}

/// An extension trait that provides a postfix version of `Scope::to_scope_from_iter`.
/// This may lead to more readable code in some instances.
pub trait CollectIntoScope<T> {
    /// A posfix version of `Scope::to_scope_from_iter`.
    /// Analogous to `Iterator::collect`.
    /// # Examples
    /// ```rust
    /// use scoped_arena::Scope;
    /// use scoped_arena::CollectIntoScope;
    ///
    /// let scope = Scope::new();
    ///
    /// let a = [1, 2, 3];
    ///
    /// let doubled: &[i32] = a.iter().map(|&x| x * 2).collect_into_scope(&scope);
    ///
    /// assert_eq!(&[2, 4, 6], doubled);
    /// ```
    #[allow(clippy::mut_from_ref)]
    fn collect_into_scope<'a>(self, scope: &'a Scope<'a>) -> &'a mut [T];
}

impl<I: IntoIterator> CollectIntoScope<I::Item> for I {
    #[inline(always)]
    fn collect_into_scope<'a>(self, scope: &'a Scope<'a>) -> &'a mut [I::Item] {
        scope.to_scope_from_iter(self)
    }
}
