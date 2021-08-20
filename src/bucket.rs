use core::{
    alloc::Layout,
    cell::Cell,
    fmt::{self, Debug},
    mem::{align_of, size_of},
    ptr::{write, NonNull},
};

use crate::allocator_api::{AllocError, Allocator};

struct Bucket {
    prev: Option<NonNull<Self>>,
    used: usize,
    layout: Layout,
}

impl Debug for Bucket {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Bucket")
            .field("used", &self.used)
            .field("layout", &self.layout)
            .finish()
    }
}

impl Bucket {
    unsafe fn init<'a>(ptr: NonNull<[u8]>, layout: Layout, list: &Buckets) -> &'a mut Self {
        debug_assert_eq!(layout.align(), align_of::<Self>());

        let ptr = ptr.cast::<Self>();
        write(
            ptr.as_ptr(),
            Bucket {
                prev: list.tail.get(),
                used: size_of::<Self>(),
                layout,
            },
        );

        list.tail.set(Some(ptr));
        list.buckets_added.set(list.buckets_added.get() + 1);
        list.last_bucket_layout.set(layout);
        list.total_memory_usage
            .set(list.total_memory_usage.get() + layout.size());

        &mut *ptr.as_ptr()
    }

    fn allocate(&mut self, layout: Layout) -> Option<NonNull<u8>> {
        let align_mask = layout.align() - 1;

        let start = self as *mut Self as usize + self.used;
        start.checked_add(align_mask)?;

        let end = self as *mut Self as usize + self.layout.size();
        let aligned = (start + align_mask) & (!align_mask);

        aligned.checked_add(layout.size())?;

        if aligned + layout.size() > end {
            // Exhausted
            return None;
        }

        self.used = aligned - self as *mut Self as usize + layout.size();

        Some(unsafe { NonNull::new_unchecked(aligned as *mut u8) })
    }

    fn reset(&mut self) {
        self.used = size_of::<Self>();
    }
}

pub struct Buckets<'a> {
    tail: Cell<Option<NonNull<Bucket>>>,
    buckets_added: Cell<usize>,
    last_bucket_layout: Cell<Layout>,
    total_memory_usage: Cell<usize>,
    parent: Option<&'a Buckets<'a>>,
    parent_tail_used: usize,
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
            .field("last_bucket_layout", &self.last_bucket_layout.get())
            .field("total_memory_usage", &self.total_memory_usage.get());

        if let Some(parent) = &self.parent {
            f.field("parent", &parent)
                .field("parent_tail_used", &self.parent_tail_used);
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
            last_bucket_layout: Cell::new(layout_with_capacity(0).ok_or(AllocError)?),
            total_memory_usage: Cell::new(0),
            parent: None,
            parent_tail_used: 0,
        };

        if capacity != 0 {
            let bucket_layout = layout_with_capacity(capacity).ok_or(AllocError)?;
            let ptr = alloc.allocate(bucket_layout)?;

            unsafe { Bucket::init(ptr, bucket_layout, &buckets) };
        }

        Ok(buckets)
    }
}

impl Buckets<'_> {
    pub unsafe fn allocate<A>(&self, layout: Layout, alloc: &A) -> Result<NonNull<u8>, AllocError>
    where
        A: Allocator,
    {
        if layout.size() == 0 {
            return Ok(NonNull::new_unchecked(layout.align() as *mut u8));
        }

        if let Some(bucket) = self.tail() {
            if let Some(ptr) = bucket.allocate(layout) {
                return Ok(ptr);
            }
        }

        // Allocate new bucket.
        let bucket_layout = next_layout(self.last_bucket_layout.get(), layout).ok_or(AllocError)?;
        let ptr = alloc.allocate(bucket_layout)?;
        self.last_bucket_layout.set(bucket_layout);
        let bucket = Bucket::init(ptr, bucket_layout, self);

        let ptr = bucket
            .allocate(layout)
            .expect("Allocation from new bucket must succeed");

        Ok(ptr)
    }

    unsafe fn tail(&self) -> Option<&mut Bucket> {
        let ptr = self.tail.get()?;
        Some(&mut *ptr.as_ptr())
    }

    pub fn fork<'a>(&'a mut self) -> Buckets<'a> {
        Buckets {
            tail: Cell::new(self.tail.get()),
            buckets_added: Cell::new(0),
            last_bucket_layout: Cell::new(self.last_bucket_layout.get()),
            total_memory_usage: Cell::new(self.total_memory_usage.get()),
            parent_tail_used: unsafe { self.tail().map_or(0, |tail| tail.used) },
            parent: Some(self),
        }
    }

    // Resets buckets added to the fork
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

                        self.total_memory_usage.set(ptr.as_ref().layout.size());
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
                    let layout = bucket.layout;
                    tail = bucket.prev;
                    alloc.deallocate(ptr.cast(), layout);
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
                            tail.used = self.parent_tail_used;
                        }
                    }
                    _ => {
                        match self.tail() {
                            None => unreachable_unchecked(),
                            Some(tail) => {
                                tail.reset();
                                let tail_used = tail.used;
                                let mut excess_bucket = tail.prev;

                                let mut memory_freed = 0;

                                // Drop all added buckets except tail.
                                for _ in 1..self.buckets_added.get() {
                                    match excess_bucket {
                                        None => unreachable_unchecked(),
                                        Some(ptr) => {
                                            let bucket = ptr.as_ref();
                                            let layout = bucket.layout;
                                            excess_bucket = bucket.prev;
                                            alloc.deallocate(ptr.cast(), layout);
                                            memory_freed += layout.size();
                                        }
                                    }
                                }

                                tail.prev = excess_bucket;

                                let total_memory_usage =
                                    parent.total_memory_usage.get() + tail.layout.size();

                                debug_assert_eq!(
                                    total_memory_usage + memory_freed,
                                    self.total_memory_usage.get()
                                );

                                parent.total_memory_usage.set(total_memory_usage);
                                parent.buckets_added.set(parent.buckets_added.get() + 1);
                                parent.last_bucket_layout.set(self.last_bucket_layout.get());
                                parent.tail.set(Some(NonNull::from(tail)));

                                self.total_memory_usage.set(total_memory_usage);
                                self.buckets_added.set(0);
                                self.parent_tail_used = tail_used;
                            }
                        }
                    }
                }
            }
        }
    }

    // Flushes buckets added to the fork.
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
                parent.last_bucket_layout.set(self.last_bucket_layout.get());
                parent.total_memory_usage.set(self.total_memory_usage.get());
            }
        }

        self.tail.set(None);
    }

    pub fn total_memory_usage(&self) -> usize {
        self.total_memory_usage.get()
    }
}

fn layout_with_capacity(capacity: usize) -> Option<Layout> {
    let (layout, _) = Layout::new::<Bucket>()
        .extend(Layout::array::<u8>(capacity).ok()?)
        .ok()?;
    Some(layout)
}

fn next_layout(last_layout: Layout, item_layout: Layout) -> Option<Layout> {
    const MIN_BUCKET_CAPACITY: usize = 128;

    let last_capacity = last_layout.size() - size_of::<Bucket>();

    let new_capacity = last_capacity
        .checked_add(last_capacity.max(item_layout.size()))?
        .max(MIN_BUCKET_CAPACITY);

    let new_align = last_layout.align();
    Layout::from_size_align(new_capacity + size_of::<Bucket>(), new_align).ok()
}
