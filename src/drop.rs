use core::{
    alloc::Layout,
    cell::Cell,
    mem::{needs_drop, size_of, ManuallyDrop, MaybeUninit},
    ptr::{drop_in_place, NonNull},
};

use crate::{cast_buf, cast_buf_array};

#[repr(C)]
pub struct WithDrop<T> {
    to_drop: ToDrop,
    value: ManuallyDrop<T>,
}

impl<T> WithDrop<T> {
    pub unsafe fn init<'a>(
        uninit: &'a mut [MaybeUninit<u8>],
        value: T,
        drop_list: &DropList,
    ) -> &'a mut T {
        debug_assert!(needs_drop::<T>());
        let uninit = cast_buf::<WithDrop<T>>(&mut uninit[..size_of::<Self>()]);

        uninit.write(WithDrop {
            to_drop: ToDrop {
                prev: drop_list.tail.get(),
                count: 1,
                drop: |_, _| {},
            },
            value: ManuallyDrop::new(value),
        });

        // Now initialized.
        let with_drop = uninit.assume_init_mut();

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

    pub unsafe fn init_iter<'a>(
        uninit: &'a mut [MaybeUninit<u8>],
        iter: impl Iterator<Item = T>,
        drop_list: &DropList,
    ) -> &'a mut [T] {
        debug_assert!(needs_drop::<T>());

        let (_, values_offset) = Layout::new::<ToDrop>().extend(Layout::new::<T>()).unwrap();
        let (to_drop_uninit, values_uninit) = uninit.split_at_mut(values_offset);

        let to_drop_uninit = cast_buf::<ToDrop>(&mut to_drop_uninit[..size_of::<ToDrop>()]);
        let to_drop = to_drop_uninit.write(ToDrop {
            prev: drop_list.tail.get(),
            count: 0,
            drop: |_, _| {},
        });

        let (values_uninit, _) = cast_buf_array::<T>(values_uninit);

        let item_count = iter.take(values_uninit.len()).fold(0, |idx, item| {
            values_uninit[idx].write(item);
            idx + 1
        });

        // Setup drop glue.
        to_drop.drop = drop_glue::<T>;
        to_drop.count = item_count;

        drop_list.tail.set(Some(NonNull::from(to_drop)));

        core::slice::from_raw_parts_mut(values_uninit.as_mut_ptr() as *mut T, item_count)
    }

    pub unsafe fn init_many<'a>(
        uninit: &'a mut [MaybeUninit<u8>],
        count: usize,
        mut f: impl FnMut() -> T,
        drop_list: &DropList,
    ) -> &'a mut [T] {
        debug_assert!(needs_drop::<T>());

        let (_, values_offset) = Layout::new::<ToDrop>().extend(Layout::new::<T>()).unwrap();
        let (to_drop_uninit, values_uninit) = uninit.split_at_mut(values_offset);

        let to_drop_uninit = cast_buf::<ToDrop>(&mut to_drop_uninit[..size_of::<ToDrop>()]);
        let to_drop = to_drop_uninit.write(ToDrop {
            prev: drop_list.tail.get(),
            count: 0,
            drop: |_, _| {},
        });

        let (values_uninit, _) = cast_buf_array::<T>(values_uninit);
        let values_uninit = &mut values_uninit[..count];

        for i in 0..count {
            values_uninit[i].write(f());
        }

        // Setup drop glue.
        to_drop.drop = drop_glue::<T>;
        to_drop.count = count;

        drop_list.tail.set(Some(NonNull::from(to_drop)));

        core::slice::from_raw_parts_mut(values_uninit.as_mut_ptr() as *mut T, count)
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
    #[inline(always)]
    pub const fn new() -> Self {
        DropList {
            tail: Cell::new(None),
            parent: None,
        }
    }

    #[inline(always)]
    pub fn fork<'a>(&'a mut self) -> DropList<'a> {
        DropList {
            tail: Cell::new(self.tail.get()),
            parent: Some(self),
        }
    }

    #[inline(always)]
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
    #[inline(always)]
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
