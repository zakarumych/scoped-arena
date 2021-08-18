//! Scoped-Arena provides arena-like allocator with optional scopes.
//! Arena allocators are simple and provides ludicrously fast allocation.
//!
//! `Scope` allows storing values. When dropped `Scope` will `Drop` all stored values and free memory allocated by the scope.\
//! Well placed scopes can significantly reduce memory consumption.\
//! Creating new scope is cheap and allocating within scope is as fast as allocating parent arena allocator.\
//! Drop glue is stored in scope only for values that `needs_drop`. i.e. for `Copy` types storing value on scope is simply allocation + copy.
//!
//! Rust borrowing rules require additional layer of `ScopeProxy` to allow references to values on scope and sub-scopes to coexist.

#![no_std]
#![cfg(any(feature = "nightly", feature = "alloc"))]
#![cfg_attr(feature = "nightly", feature(allocator_api))]

#[cfg(feature = "alloc")]
extern crate alloc;

mod bucket;
mod drop;
mod stable_alloc;

use core::{
    alloc::Layout,
    fmt::{self, Debug},
    iter::IntoIterator,
    mem::needs_drop,
    ptr::{write, NonNull},
};

#[cfg(all(not(no_global_oom_handling), feature = "alloc"))]
use alloc::alloc::handle_alloc_error;

use self::{
    bucket::Buckets,
    drop::{DropList, WithDrop},
};

pub use self::stable_alloc::{AllocError, Allocator};

#[cfg(feature = "alloc")]
pub use self::stable_alloc::Global;

struct OwnedBuckets(Buckets<'static>);

// # Safety
// OwnedBuckets can be moved to another thread as owned value of `OwnedBuckets` doesn't share references to its interior.
// OwnedBuckets cannot be `Sync` though.
unsafe impl Send for OwnedBuckets {}

/// Arena allocator with support for scope based memory reclamation.
/// This type is a wrapper over underlying allocator
/// which provides sub-allocations with amortized cost of just few CPU instructions.
#[cfg(not(feature = "alloc"))]
pub struct Arena<A: Allocator> {
    buckets: OwnedBuckets,
    alloc: A,
}

/// Arena allocator with support for scope based memory reclamation.
/// This type is a wrapper over underlying allocator
/// which provides sub-allocations with amortized cost of just few CPU instructions.
#[cfg(feature = "alloc")]
pub struct Arena<A: Allocator = Global> {
    buckets: OwnedBuckets,
    alloc: A,
}

impl<A> Debug for Arena<A>
where
    A: Allocator,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Arena")
            .field("buckets", &self.buckets.0)
            .finish_non_exhaustive()
    }
}

impl<A> Drop for Arena<A>
where
    A: Allocator,
{
    fn drop(&mut self) {
        unsafe { self.buckets.0.reset(&self.alloc, false) }
    }
}

impl<A> Arena<A>
where
    A: Allocator,
{
    /// Reset pre-allocated memory.
    /// Keeps only last memory allocated from underlying allocator
    /// and resets its usage.
    ///
    /// This method is safe due to guarantee that all memory allocated
    /// can't be accessed without some unsafe code breaking safety contract.
    pub fn reset(&mut self) {
        unsafe { self.buckets.0.reset(&self.alloc, true) }
    }
}

#[cfg(feature = "alloc")]
impl Arena<Global> {
    /// Returns new instance of arena allocator based on [`Global`] allocator.
    pub fn new() -> Self {
        Arena::new_in(Global)
    }

    /// Returns new instance of arena allocator based on [`Global`] allocator
    /// with preallocated capacity in bytes.
    pub fn with_capacity(capacity: usize) -> Self {
        Arena::with_capacity_in(capacity, Global)
    }
}

impl<A> Arena<A>
where
    A: Allocator,
{
    /// Returns new instance of arena allocator based on provided allocator.
    pub fn new_in(alloc: A) -> Self {
        Arena::with_capacity_in(0, alloc)
    }

    /// Returns new instance of arena allocator based on provided allocator
    /// with preallocated capacity in bytes.
    pub fn with_capacity_in(capacity: usize, alloc: A) -> Self {
        Arena {
            buckets: OwnedBuckets(
                Buckets::new(capacity, &alloc).expect(ALLOCATOR_CAPACITY_OVERFLOW),
            ),
            alloc,
        }
    }

    /// Allocates a block of memory.
    /// Returns a [`NonNull<u8>`] meeting the size and alignment guarantees of layout.
    /// The returned block contents should be considered uninitialized.
    ///
    /// Returned block will be deallocated when arena is reset ([`Arena::reset`]) or dropped.
    #[cfg(all(not(no_global_oom_handling), feature = "alloc"))]
    pub fn alloc(&self, layout: Layout) -> NonNull<u8> {
        match self.try_alloc(layout) {
            Ok(ptr) => ptr,
            Err(_) => handle_alloc_error(layout),
        }
    }

    /// Attempts to allocate a block of memory.
    /// On success, returns a [`NonNull<u8>`] meeting the size and alignment guarantees of layout.
    /// The returned block contents should be considered uninitialized.
    ///
    /// Returned block will be deallocated when arena is reset ([`Arena::reset`]) or dropped.
    ///
    /// # Errors
    ///
    /// Returning `Err` indicates that memory is exhausted.
    pub fn try_alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        unsafe { self.buckets.0.allocate(layout, &self.alloc) }
    }

    /// Creates new scope for the arena.
    /// Returns [`Scope`] instance which can be used to allocate memory and place values into the scope.
    /// Upon drop, scope will drop all values and free allocated memory.
    pub fn scope(&mut self) -> Scope<'_, A> {
        Scope {
            buckets: self.buckets.0.fork(),
            alloc: &self.alloc,
            drop_list: DropList::new(),
        }
    }

    /// Reports total memory allocated from underlying allocator by this arena.
    pub fn total_memory_usage(&self) -> usize {
        self.buckets.0.total_memory_usage()
    }
}

/// Scope associated with `Arena` allocator.
/// Allows placing values on the scope returning reference bound to scope borrow.
/// On drop scope drops all values placed onto it.
/// On drop scope frees all memory allocated from it.
#[cfg(not(feature = "alloc"))]
pub struct Scope<'arena, A: Allocator> {
    buckets: Buckets<'arena>,
    alloc: &'arena A,
    drop_list: DropList<'static>,
}

/// Scope associated with `Arena` allocator.
/// Allows placing values on the scope returning reference bound to scope borrow.
/// On drop scope drops all values placed onto it.
/// On drop scope frees all memory allocated from it.
#[cfg(feature = "alloc")]
pub struct Scope<'arena, A: Allocator = Global> {
    buckets: Buckets<'arena>,
    alloc: &'arena A,
    drop_list: DropList<'static>,
}

impl<A> Debug for Scope<'_, A>
where
    A: Allocator,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Region")
            .field("buckets", &self.buckets)
            .finish_non_exhaustive()
    }
}

impl<A> Drop for Scope<'_, A>
where
    A: Allocator,
{
    fn drop(&mut self) {
        unsafe {
            self.drop_list.reset();
            self.buckets.reset_fork(self.alloc);
        }
    }
}

impl<A> Scope<'_, A>
where
    A: Allocator,
{
    /// Allocates a block of memory.
    /// Returns a [`NonNull<u8>`] meeting the size and alignment guarantees of layout.
    /// The returned block contents should be considered uninitialized.
    ///
    /// Returned block will be deallocated when scope is dropped.
    #[cfg(all(not(no_global_oom_handling), feature = "alloc"))]
    pub fn alloc(&self, layout: Layout) -> NonNull<u8> {
        match self.try_alloc(layout) {
            Ok(ptr) => ptr,
            Err(_) => handle_alloc_error(layout),
        }
    }

    /// Attempts to allocate a block of memory.
    /// On success, returns a [`NonNull<u8>`] meeting the size and alignment guarantees of layout.
    /// The returned block contents should be considered uninitialized.
    ///
    /// Returned block will be deallocated when scope is dropped.
    ///
    /// # Errors
    ///
    /// Returning `Err` indicates that memory is exhausted.
    pub fn try_alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        unsafe { self.buckets.allocate(layout, self.alloc) }
    }

    /// Move value onto the scope.
    /// Returns mutable reference to value with lifetime equal to scope borrow lifetime.
    /// Value on scope will be dropped when scope is dropped.
    ///
    /// This method is as cheap as allocation if value does not needs dropping as reported by [`core::mem::needs_drop`].
    #[cfg(all(not(no_global_oom_handling), feature = "alloc"))]
    pub fn to_scope<T>(&self, value: T) -> &mut T {
        match self.try_to_scope(value) {
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
    pub fn try_to_scope<T>(&self, value: T) -> Result<&mut T, (AllocError, T)> {
        if needs_drop::<T>() {
            match self.try_alloc(Layout::new::<WithDrop<T>>()) {
                Ok(ptr) => {
                    let ptr = ptr.cast::<WithDrop<T>>();

                    let value = unsafe { WithDrop::init(ptr, value, &self.drop_list) };
                    Ok(value)
                }
                Err(err) => Err((err, value)),
            }
        } else {
            match self.try_alloc(Layout::new::<T>()) {
                Ok(ptr) => {
                    let ptr = ptr.cast::<T>();
                    unsafe { write(ptr.as_ptr(), value) };
                    Ok(unsafe { &mut *ptr.as_ptr() })
                }
                Err(err) => Err((err, value)),
            }
        }
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
    pub fn to_scope_from_iter<T, I>(&self, iter: I) -> &mut [T]
    where
        I: IntoIterator<Item = T>,
    {
        use core::mem::align_of;

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
    pub fn try_to_scope_from_iter<T, I>(
        &self,
        iter: I,
    ) -> Result<&mut [T], (AllocError, I::IntoIter)>
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
                Some(layout) => match self.try_alloc(layout) {
                    Ok(ptr) => {
                        let ptr = ptr.cast::<WithDrop<T>>();
                        let slice = unsafe { WithDrop::init_array(ptr, iter, &self.drop_list) };
                        Ok(slice)
                    }
                    Err(err) => Err((err, iter)),
                },
                None => Err((AllocError, iter)),
            }
        } else {
            match Layout::array::<T>(upper_bound) {
                Ok(layout) => match self.try_alloc(layout) {
                    Ok(ptr) => {
                        let ptr = ptr.cast::<T>();

                        let mut item_count = 0;
                        unsafe {
                            for item in iter.take(upper_bound) {
                                write(ptr.as_ptr().add(item_count), item);
                                item_count += 1;
                            }
                        }

                        let slice =
                            unsafe { core::slice::from_raw_parts_mut(ptr.as_ptr(), item_count) };
                        Ok(&mut *slice)
                    }
                    Err(err) => Err((err, iter)),
                },
                Err(_) => Err((AllocError, iter)),
            }
        }
    }

    /// Reports total memory allocated from underlying allocator by associated arena.
    pub fn total_memory_usage(&self) -> usize {
        self.buckets.total_memory_usage()
    }

    /// Creates new scope which inherits this scope.
    /// This scope becomes locked until returned scope is dropped.
    pub fn scope(&mut self) -> Scope<'_, A> {
        Scope {
            buckets: self.buckets.fork(),
            alloc: self.alloc,
            drop_list: DropList::new(),
        }
    }

    /// Creates scope proxy bound to the scope.
    pub fn proxy(&mut self) -> ScopeProxy<'_, A> {
        ScopeProxy {
            buckets: self.buckets.fork(),
            alloc: self.alloc,
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
    alloc: &'scope A,
    drop_list: DropList<'scope>,
}

impl<A> Debug for ScopeProxy<'_, A>
where
    A: Allocator,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ScopeRef")
            .field("buckets", &self.buckets)
            .finish_non_exhaustive()
    }
}

impl<A> Drop for ScopeProxy<'_, A>
where
    A: Allocator,
{
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
    /// Returns a [`NonNull<u8>`] meeting the size and alignment guarantees of layout.
    /// The returned block contents should be considered uninitialized.
    ///
    /// Returned block will be deallocated when scope is dropped.
    #[cfg(all(not(no_global_oom_handling), feature = "alloc"))]
    pub fn alloc(&self, layout: Layout) -> NonNull<u8> {
        match self.try_alloc(layout) {
            Ok(ptr) => ptr,
            Err(_) => handle_alloc_error(layout),
        }
    }

    /// Attempts to allocate a block of memory.
    /// On success, returns a [`NonNull<u8>`] meeting the size and alignment guarantees of layout.
    /// The returned block contents should be considered uninitialized.
    ///
    /// Returned block will be deallocated when scope is dropped.
    ///
    /// # Errors
    ///
    /// Returning `Err` indicates that memory is exhausted.
    pub fn try_alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        unsafe { self.buckets.allocate(layout, self.alloc) }
    }

    /// Move value onto the scope.
    /// Returns mutable reference to value with lifetime equal to 'scope lifetime.
    /// Value on scope will be dropped when scope is dropped.
    ///
    /// This method is as cheap as allocation if value does not needs dropping as reported by [`core::mem::needs_drop`].
    #[cfg(all(not(no_global_oom_handling), feature = "alloc"))]
    pub fn to_scope<T>(&self, value: T) -> &'scope mut T {
        match self.try_to_scope(value) {
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
    pub fn try_to_scope<T>(&self, value: T) -> Result<&'scope mut T, (AllocError, T)> {
        if needs_drop::<T>() {
            match self.try_alloc(Layout::new::<WithDrop<T>>()) {
                Ok(ptr) => {
                    let ptr = ptr.cast::<WithDrop<T>>();

                    let value = unsafe { WithDrop::init(ptr, value, &self.drop_list) };
                    Ok(value)
                }
                Err(err) => Err((err, value)),
            }
        } else {
            match self.try_alloc(Layout::new::<T>()) {
                Ok(ptr) => {
                    let ptr = ptr.cast::<T>();
                    unsafe { write(ptr.as_ptr(), value) };
                    Ok(unsafe { &mut *ptr.as_ptr() })
                }
                Err(err) => Err((err, value)),
            }
        }
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
    pub fn to_scope_from_iter<T, I>(&self, iter: I) -> &'scope mut [T]
    where
        I: IntoIterator<Item = T>,
    {
        use core::mem::align_of;

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
    pub fn try_to_scope_from_iter<T, I>(
        &self,
        iter: I,
    ) -> Result<&'scope mut [T], (AllocError, I::IntoIter)>
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
                Some(layout) => match self.try_alloc(layout) {
                    Ok(ptr) => {
                        let ptr = ptr.cast::<WithDrop<T>>();
                        let slice = unsafe { WithDrop::init_array(ptr, iter, &self.drop_list) };
                        Ok(slice)
                    }
                    Err(err) => Err((err, iter)),
                },
                None => Err((AllocError, iter)),
            }
        } else {
            match Layout::array::<T>(upper_bound) {
                Ok(layout) => match self.try_alloc(layout) {
                    Ok(ptr) => {
                        let ptr = ptr.cast::<T>();

                        let mut item_count = 0;
                        unsafe {
                            for item in iter.take(upper_bound) {
                                write(ptr.as_ptr().add(item_count), item);
                                item_count += 1;
                            }
                        }

                        let slice =
                            unsafe { core::slice::from_raw_parts_mut(ptr.as_ptr(), item_count) };
                        Ok(&mut *slice)
                    }
                    Err(err) => Err((err, iter)),
                },
                Err(_) => Err((AllocError, iter)),
            }
        }
    }

    /// Reports total memory allocated from underlying allocator by associated arena.
    pub fn total_memory_usage(&self) -> usize {
        self.buckets.total_memory_usage()
    }

    /// Creates new scope which inherits this scope.
    /// This scope becomes locked until returned scope is dropped.
    pub fn scope(&mut self) -> Scope<'_, A> {
        Scope {
            buckets: self.buckets.fork(),
            alloc: self.alloc,
            drop_list: DropList::new(),
        }
    }
}

const ALLOCATOR_CAPACITY_OVERFLOW: &'static str = "Allocator capacity overflow";

unsafe impl<A> Allocator for &'_ Arena<A>
where
    A: Allocator,
{
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        let ptr = self.try_alloc(layout)?;
        let slice = unsafe {
            // `Arena` always allocates exact amount of bytes.
            NonNull::new_unchecked(core::slice::from_raw_parts_mut(ptr.as_ptr(), layout.size()))
        };
        Ok(slice)
    }

    unsafe fn deallocate(&self, _ptr: NonNull<u8>, _layout: Layout) {
        // Will be deallocated on arena reset.
    }

    #[cfg(feature = "nightly")]
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

unsafe impl<A> Allocator for &'_ Scope<'_, A>
where
    A: Allocator,
{
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        let ptr = self.try_alloc(layout)?;
        let slice = unsafe {
            // `ScopeProxy` always allocates exact amount of bytes.
            NonNull::new_unchecked(core::slice::from_raw_parts_mut(ptr.as_ptr(), layout.size()))
        };
        Ok(slice)
    }

    unsafe fn deallocate(&self, _ptr: NonNull<u8>, _layout: Layout) {
        // Will be deallocated on scope drop.
    }

    #[cfg(feature = "nightly")]
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

unsafe impl<A> Allocator for &'_ ScopeProxy<'_, A>
where
    A: Allocator,
{
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        let ptr = self.try_alloc(layout)?;
        let slice = unsafe {
            // `ScopeProxy` always allocates exact amount of bytes.
            NonNull::new_unchecked(core::slice::from_raw_parts_mut(ptr.as_ptr(), layout.size()))
        };
        Ok(slice)
    }

    unsafe fn deallocate(&self, _ptr: NonNull<u8>, _layout: Layout) {
        // Will be deallocated on scope drop.
    }

    #[cfg(feature = "nightly")]
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
