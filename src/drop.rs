use core::{
    alloc::Layout,
    cell::Cell,
    mem::{needs_drop, ManuallyDrop},
    ptr::{drop_in_place, write, NonNull},
};

#[repr(C)]
pub struct WithDrop<T> {
    to_drop: ToDrop,
    value: ManuallyDrop<T>,
}

impl<T> WithDrop<T> {
    pub unsafe fn init<'a>(ptr: NonNull<Self>, value: T, drop_list: &DropList) -> &'a mut T {
        debug_assert!(needs_drop::<T>());

        // Pointer is expected to suitable for `WithDrop<T>`.
        write(
            ptr.as_ptr(),
            WithDrop {
                to_drop: ToDrop {
                    prev: drop_list.tail.get(),
                    count: 1,
                    drop: |_, _| {},
                },
                value: ManuallyDrop::new(value),
            },
        );

        // Now initialized.
        let with_drop = &mut *ptr.as_ptr();

        // Setup drop glue.
        with_drop.to_drop.drop = drop_glue::<T>;

        drop_list
            .tail
            .set(Some(NonNull::from(&mut with_drop.to_drop)));

        &mut *with_drop.value
    }

    pub fn array_layout(count: usize) -> Option<Layout> {
        Some(
            Layout::new::<ToDrop>()
                .extend(Layout::array::<T>(count).ok()?)
                .ok()?
                .0,
        )
    }

    pub unsafe fn init_array<'a>(
        ptr: NonNull<Self>,
        iter: impl Iterator<Item = T>,
        drop_list: &DropList,
    ) -> &'a mut [T] {
        debug_assert!(needs_drop::<T>());

        let to_drop_ptr = ptr.as_ptr().cast::<ToDrop>();

        write(
            to_drop_ptr,
            ToDrop {
                prev: drop_list.tail.get(),
                count: 0,
                drop: |_, _| {},
            },
        );

        let items_start_ptr = to_drop_ptr.add(1).cast::<T>();

        let upper_bound = iter.size_hint().1.unwrap();
        let mut item_count = 0;
        for item in iter.take(upper_bound) {
            write(items_start_ptr.add(item_count), item);
            item_count += 1;
        }

        // Now initialized.
        let to_drop = &mut *to_drop_ptr;

        // Setup drop glue.
        to_drop.drop = drop_glue::<T>;
        to_drop.count = item_count;

        drop_list.tail.set(Some(NonNull::from(to_drop)));

        let slice = core::slice::from_raw_parts_mut(items_start_ptr, item_count);
        &mut *slice
    }
}

pub struct DropList<'a> {
    tail: Cell<Option<NonNull<ToDrop>>>,
    parent: Option<&'a Self>,
}

#[cfg(debug_assertions)]
impl Drop for DropList<'_> {
    fn drop(&mut self) {
        assert!(self.tail.get().is_none());
    }
}

impl DropList<'static> {
    pub fn new() -> Self {
        DropList {
            tail: Cell::new(None),
            parent: None,
        }
    }

    pub fn fork<'a>(&'a mut self) -> DropList<'a> {
        DropList {
            tail: Cell::new(self.tail.get()),
            parent: Some(self),
        }
    }

    pub unsafe fn reset(&mut self) {
        debug_assert!(self.parent.is_none());

        let mut tail = self.tail.get();
        while let Some(ptr) = tail.take() {
            let to_drop = ptr.as_ref();
            (to_drop.drop)(ptr, to_drop.count);
            tail = to_drop.prev;
        }

        self.tail.set(None);
    }
}

impl DropList<'_> {
    // Flushes drops added to the fork.
    pub unsafe fn flush_fork(&mut self) {
        use core::hint::unreachable_unchecked;

        debug_assert!(
            self.parent.is_some(),
            "Must be called only on non-root bucket list owned by `Scope`"
        );

        match self.parent {
            None => unreachable_unchecked(),
            Some(parent) => {
                parent.tail.set(self.tail.get());
            }
        }

        self.tail.set(None);
    }
}

struct ToDrop {
    prev: Option<NonNull<Self>>,
    count: usize,
    drop: unsafe fn(NonNull<Self>, usize),
}

unsafe fn drop_glue<T>(ptr: NonNull<ToDrop>, count: usize) {
    // `ptr` is `ToDrop` field of `WithDrop<T>`
    // `value` field is next to `ToDrop` field.

    let offset = Layout::new::<ToDrop>()
        .extend(Layout::new::<T>())
        .unwrap()
        .1;

    drop_in_place(core::slice::from_raw_parts_mut(
        ptr.as_ptr().cast::<u8>().add(offset).cast::<T>(),
        count,
    ))
}
