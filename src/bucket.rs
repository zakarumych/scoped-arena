use core::{
    alloc::Layout,
    cell::Cell,
    fmt::{self, Debug},
    mem::{align_of, size_of, MaybeUninit},
    ptr::{write, NonNull},
};

use crate::allocator_api::{AllocError, Allocator};

struct BucketFooter {
    prev: Option<NonNull<Self>>,
    start: NonNull<u8>,
    free_end: usize,
    size: usize,
}

impl Debug for BucketFooter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Bucket")
            .field("start", &self.start)
            .field("size", &self.size)
            .field("free_end", &(self.free_end as *mut u8))
            .field("free", &(self.free_end - self.start.as_ptr() as usize))
            .finish()
    }
}

impl BucketFooter {
    unsafe fn init<'a>(ptr: NonNull<[u8]>, list: &Buckets) -> &'a mut Self {
        let slice = &mut *(ptr.as_ptr() as *mut [MaybeUninit<u8>]);
        let size = slice.len();

        let start = NonNull::new_unchecked(slice.as_mut_ptr().cast::<u8>());

        let cap = (size - size_of::<Self>()) & !(align_of::<Self>() - 1);
        let end = start.as_ptr() as usize + cap;

        let footer_ptr = start.as_ptr().add(cap).cast::<Self>();
        write(
            footer_ptr,
            BucketFooter {
                prev: list.tail.get(),
                start,
                free_end: end,
                size,
            },
        );

        list.tail.set(Some(NonNull::new_unchecked(footer_ptr)));
        list.buckets_added.set(list.buckets_added.get() + 1);

        list.last_bucket_size.set(size);
        list.total_memory_usage
            .set(list.total_memory_usage.get() + size);

        &mut *footer_ptr
    }

    #[inline(always)]
    fn allocate(&mut self, layout: Layout) -> Option<NonNull<[u8]>> {
        let aligned = self.free_end.checked_sub(layout.size())? & !(layout.align() - 1);

        if aligned >= self.start.as_ptr() as usize {
            let aligned_ptr = aligned as *mut u8;
            let slice = core::ptr::slice_from_raw_parts_mut(aligned_ptr, self.free_end - aligned);
            self.free_end = aligned;

            Some(unsafe { NonNull::new_unchecked(slice) })
        } else {
            None
        }
    }

    #[inline(always)]
    fn reset(&mut self) {
        let cap = (self.size - size_of::<Self>()) & !(align_of::<Self>() - 1);
        self.free_end = self.start.as_ptr() as usize + cap;
    }
}

pub struct Buckets<'a> {
    tail: Cell<Option<NonNull<BucketFooter>>>,
    buckets_added: Cell<usize>,
    last_bucket_size: Cell<usize>,
    total_memory_usage: Cell<usize>,
    parent: Option<&'a Buckets<'a>>,
    parent_tail_free_end: usize,
}

/// This type does not automatically implement `Send` because of `NonNull` pointer and reference to Self which is not Sync.
/// NonNull pointer is tail of the list of allocated buckets owned by the bucket and parent.
/// When buckets instance with parent is constructed parent is borrowed mutably, so parent cannot be used from another thread.
/// This also grants exclusive access to the buckets list.
unsafe impl Send for Buckets<'_> {}

#[cfg(debug_assertions)]
impl Drop for Buckets<'_> {
    fn drop(&mut self) {
        if self.parent.is_none() {
            assert!(self.tail.get().is_none());
        }
    }
}

impl Debug for Buckets<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut f = f.debug_struct("BucketAlloc");
        f.field("buckets_added", &self.buckets_added.get())
            .field("last_bucket_size", &self.last_bucket_size.get())
            .field("total_memory_usage", &self.total_memory_usage.get());

        if let Some(parent) = &self.parent {
            f.field("parent", &parent)
                .field("parent_tail_used", &self.parent_tail_free_end);
        }

        let mut tail = self.tail.get();
        while let Some(ptr) = tail {
            let b = unsafe { ptr.as_ref() };
            f.field("elem", b);
            tail = b.prev;
        }

        f.finish()
    }
}

impl Buckets<'static> {
    pub fn new<A>(capacity: usize, alloc: &A) -> Result<Self, AllocError>
    where
        A: Allocator,
    {
        let buckets = Buckets {
            tail: Cell::new(None),
            buckets_added: Cell::new(0),
            last_bucket_size: Cell::new(0),
            total_memory_usage: Cell::new(0),
            parent: None,
            parent_tail_free_end: 0,
        };

        if capacity != 0 {
            let bucket_layout = layout_with_capacity(capacity).ok_or(AllocError)?;
            let ptr = alloc.allocate(bucket_layout)?;

            unsafe { BucketFooter::init(ptr, &buckets) };
        }

        Ok(buckets)
    }
}

impl Buckets<'_> {
    #[inline(always)]
    pub unsafe fn allocate<A>(&self, layout: Layout, alloc: &A) -> Result<NonNull<[u8]>, AllocError>
    where
        A: Allocator,
    {
        if layout.size() == 0 {
            return Ok(NonNull::new_unchecked(core::ptr::slice_from_raw_parts_mut(
                layout.align() as *mut u8,
                0,
            )));
        }

        if let Some(bucket) = self.tail() {
            if let Some(ptr) = bucket.allocate(layout) {
                return Ok(ptr);
            }
        }

        // Allocate new bucket.
        let bucket_layout = next_layout(self.last_bucket_size.get(), layout).ok_or(AllocError)?;
        let ptr = alloc.allocate(bucket_layout)?;
        self.last_bucket_size.set(bucket_layout.size());
        let bucket = BucketFooter::init(ptr, self);

        let ptr = bucket
            .allocate(layout)
            .expect("Allocation from new bucket must succeed");

        Ok(ptr)
    }

    unsafe fn tail(&self) -> Option<&mut BucketFooter> {
        let ptr = self.tail.get()?;
        Some(&mut *ptr.as_ptr())
    }

    #[inline(always)]
    pub fn fork<'a>(&'a mut self) -> Buckets<'a> {
        Buckets {
            tail: Cell::new(self.tail.get()),
            buckets_added: Cell::new(0),
            last_bucket_size: Cell::new(self.last_bucket_size.get()),
            total_memory_usage: Cell::new(self.total_memory_usage.get()),
            parent_tail_free_end: unsafe { self.tail().map_or(0, |tail| tail.free_end) },
            parent: Some(self),
        }
    }

    // Resets buckets added to the fork
    #[inline(always)]
    pub unsafe fn reset<A>(&mut self, alloc: &A, keep_tail: bool)
    where
        A: Allocator,
    {
        use core::hint::unreachable_unchecked;

        match &self.parent {
            None => {
                // Resetting root.
                let mut tail = self.tail.get();
                let pre_reset_total_memory_usage = self.total_memory_usage.get();

                if keep_tail {
                    if let Some(mut ptr) = tail {
                        let prev = ptr.as_ref().prev;
                        ptr.as_mut().prev = None;
                        ptr.as_mut().reset();
                        tail = prev;

                        self.total_memory_usage.set(ptr.as_ref().size);
                    } else {
                        debug_assert_eq!(self.total_memory_usage.get(), 0);
                    }
                } else {
                    self.tail.set(None);
                    self.total_memory_usage.set(0);
                }

                let post_reset_total_memory_usage = self.total_memory_usage.get();
                let mut memory_freed = 0;

                while let Some(ptr) = tail {
                    let bucket = ptr.as_ref();
                    let layout =
                        Layout::from_size_align_unchecked(bucket.size, align_of::<BucketFooter>());
                    tail = bucket.prev;
                    alloc.deallocate(bucket.start, layout);
                    memory_freed += layout.size();
                }

                debug_assert_eq!(
                    post_reset_total_memory_usage + memory_freed,
                    pre_reset_total_memory_usage
                );
            }
            Some(parent) => {
                // Resetting scoped arena
                match self.buckets_added.get() {
                    0 => {
                        if let Some(tail) = parent.tail() {
                            tail.free_end = self.parent_tail_free_end;
                        }
                    }
                    _ => {
                        match self.tail() {
                            None => unreachable_unchecked(),
                            Some(tail) => {
                                tail.reset();
                                let mut excess_bucket = tail.prev;

                                let mut memory_freed = 0;

                                // Drop all added buckets except tail.
                                for _ in 1..self.buckets_added.get() {
                                    match excess_bucket {
                                        None => unreachable_unchecked(),
                                        Some(ptr) => {
                                            let bucket = ptr.as_ref();
                                            let layout = Layout::from_size_align_unchecked(
                                                bucket.size,
                                                align_of::<BucketFooter>(),
                                            );
                                            excess_bucket = bucket.prev;
                                            alloc.deallocate(bucket.start, layout);
                                            memory_freed += layout.size();
                                        }
                                    }
                                }

                                tail.prev = excess_bucket;
                                let tail_free_end = tail.free_end;

                                let total_memory_usage =
                                    parent.total_memory_usage.get() + tail.size;

                                debug_assert_eq!(
                                    total_memory_usage + memory_freed,
                                    self.total_memory_usage.get()
                                );

                                parent.total_memory_usage.set(total_memory_usage);
                                parent.buckets_added.set(parent.buckets_added.get() + 1);
                                parent.last_bucket_size.set(self.last_bucket_size.get());
                                parent.tail.set(Some(NonNull::from(tail)));

                                self.total_memory_usage.set(total_memory_usage);
                                self.buckets_added.set(0);
                                self.parent_tail_free_end = tail_free_end;
                            }
                        }
                    }
                }
            }
        }
    }

    // Flushes buckets added to the fork.
    #[inline(always)]
    pub unsafe fn flush_fork(&mut self) {
        use core::hint::unreachable_unchecked;

        debug_assert!(
            self.parent.is_some(),
            "Must be called only on non-root bucket list owned by `Scope`"
        );

        match &self.parent {
            None => unreachable_unchecked(),
            Some(parent) => {
                parent.tail.set(self.tail.get());
                parent
                    .buckets_added
                    .set(parent.buckets_added.get() + self.buckets_added.get());
                parent.last_bucket_size.set(self.last_bucket_size.get());
                parent.total_memory_usage.set(self.total_memory_usage.get());
            }
        }

        self.tail.set(None);
    }

    #[inline(always)]
    pub fn total_memory_usage(&self) -> usize {
        self.total_memory_usage.get()
    }
}

fn layout_with_capacity(capacity: usize) -> Option<Layout> {
    let (layout, _) = Layout::new::<BucketFooter>()
        .extend(Layout::array::<u8>(capacity).ok()?)
        .ok()?;
    Some(layout)
}

fn next_layout(last_size: usize, item_layout: Layout) -> Option<Layout> {
    const ALIGN: usize = 1 + ((align_of::<BucketFooter>() - 1) | 7);
    const BIG_ALIGN: usize = 1 + (((1 << 12) - 1) | (ALIGN - 1));
    const FOOTER_OVERHEAD: usize = size_of::<BucketFooter>() + ALIGN;
    const MIN_CAP: usize = 32;

    let min_grow = (item_layout.size() + item_layout.align() - 1)
        .max(MIN_CAP)
        .checked_add(FOOTER_OVERHEAD)?;
    let grow = last_size.max(min_grow);
    let size = last_size.checked_add(grow)?;

    let aligned_size = if size > BIG_ALIGN {
        size.checked_add(BIG_ALIGN - 1)? & !(BIG_ALIGN - 1)
    } else {
        size.checked_add(ALIGN - 1)? & !(ALIGN - 1)
    };

    Layout::from_size_align(aligned_size, ALIGN).ok()
}
