use std::{
    cell::UnsafeCell,
    mem::MaybeUninit,
    ptr,
    sync::atomic::{AtomicBool, AtomicPtr, AtomicUsize, Ordering},
};

const POINTER_WIDTH: u8 = usize::BITS as u8;

/// The total number of buckets stored in each thread local.
/// All buckets combined can hold up to `2^POINTER_WIDTH - 1` entries.
const BUCKETS: usize = (POINTER_WIDTH - 1) as usize;

/// Lock-free, append-only dynamic array.
pub(crate) struct AppendOnlyVec<T: Send> {
    /// The `n`th bucket contains `2^n` elements. Each bucket is lazily allocated.
    buckets: Box<[AtomicPtr<Entry<T>>; BUCKETS]>,
    len: AtomicUsize,
}

struct Entry<T> {
    present: AtomicBool,
    value: UnsafeCell<MaybeUninit<T>>,
}

impl<T> Drop for Entry<T> {
    fn drop(&mut self) {
        if *self.present.get_mut() {
            unsafe { ptr::drop_in_place(self.value.get_mut().as_mut_ptr()) };
        }
    }
}

unsafe impl<T: Send> Sync for AppendOnlyVec<T> {}

impl<T: Send> Default for AppendOnlyVec<T> {
    fn default() -> AppendOnlyVec<T> {
        AppendOnlyVec::new()
    }
}

impl<T: Send> Drop for AppendOnlyVec<T> {
    fn drop(&mut self) {
        for (i, bucket) in self.buckets.iter_mut().enumerate() {
            let bucket_ptr = *bucket.get_mut();
            if bucket_ptr.is_null() {
                continue;
            }
            unsafe { deallocate_bucket(bucket_ptr, bucket_len(i)) };
        }
    }
}

impl<T: Send> AppendOnlyVec<T> {
    pub(crate) fn new() -> AppendOnlyVec<T> {
        let buckets = Box::new([const { AtomicPtr::<Entry<T>>::new(ptr::null_mut()) }; BUCKETS]);
        Self { buckets, len: AtomicUsize::new(0) }
    }

    pub(crate) fn with_capacity(capacity: usize) -> AppendOnlyVec<T> {
        let mut this = Self::new();

        let Indexes { bucket, .. } = indexes(capacity);
        for (i, bucket) in this.buckets[..bucket].iter_mut().enumerate() {
            *bucket.get_mut() = allocate_bucket::<T>(bucket_len(i));
        }

        this
    }

    pub(crate) fn len(&self) -> usize {
        self.len.load(Ordering::Relaxed)
    }

    pub(crate) fn push(&self, value: T) -> usize {
        let i = self.len.fetch_add(1, Ordering::Relaxed);
        let Indexes { bucket, index, bucket_size } = indexes(i);

        let bucket_atomic_ptr = unsafe { self.buckets.get_unchecked(bucket) };
        let bucket_ptr = bucket_atomic_ptr.load(Ordering::Acquire);

        // If the bucket doesn't already exist, we need to allocate it
        let bucket_ptr = if bucket_ptr.is_null() {
            let new_bucket = allocate_bucket(bucket_size);

            match bucket_atomic_ptr.compare_exchange(
                ptr::null_mut(),
                new_bucket,
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => new_bucket,
                // If the bucket value changed (from null), that means
                // another thread stored a new bucket before we could,
                // and we can free our bucket and use that one instead
                Err(bucket_ptr) => {
                    unsafe { deallocate_bucket(new_bucket, bucket_size) }
                    bucket_ptr
                }
            }
        } else {
            bucket_ptr
        };

        // Insert the new element into the bucket
        let entry = unsafe { &*bucket_ptr.add(index) };
        let value_ptr = entry.value.get();
        unsafe { value_ptr.write(MaybeUninit::new(value)) };
        entry.present.store(true, Ordering::Release);

        i
    }

    pub(crate) fn get(&self, index: usize) -> Option<&T> {
        let Indexes { bucket, index, bucket_size: _ } = indexes(index);
        let bucket_ptr = unsafe { self.buckets.get_unchecked(bucket) }.load(Ordering::Acquire);
        if bucket_ptr.is_null() {
            return None;
        }
        unsafe {
            let entry = &*bucket_ptr.add(index);
            if entry.present.load(Ordering::Relaxed) {
                Some(&*(*entry.value.get()).as_ptr())
            } else {
                None
            }
        }
    }

    pub(crate) unsafe fn get_unchecked(&self, index: usize) -> &T {
        unsafe { self.get(index).unwrap_unchecked() }
    }

    #[cfg(test)]
    fn count_buckets(&self) -> usize {
        self.buckets.iter().filter(|b| !b.load(Ordering::Relaxed).is_null()).count()
    }
}

struct Indexes {
    bucket: usize,
    index: usize,
    bucket_size: usize,
}

#[inline]
fn indexes(i: usize) -> Indexes {
    let bucket = usize::from(POINTER_WIDTH) - ((i + 1).leading_zeros() as usize) - 1;
    let bucket_size = bucket_len(bucket);
    let index = i - (bucket_size - 1);
    Indexes { bucket, index, bucket_size }
}

#[inline]
fn bucket_len(bucket: usize) -> usize {
    1 << bucket
}

fn allocate_bucket<T>(size: usize) -> *mut Entry<T> {
    Box::into_raw(
        (0..size)
            .map(|_| Entry::<T> {
                present: AtomicBool::new(false),
                value: UnsafeCell::new(MaybeUninit::uninit()),
            })
            .collect(),
    ) as *mut _
}

unsafe fn deallocate_bucket<T>(bucket: *mut Entry<T>, size: usize) {
    let _ = Box::from_raw(std::ptr::slice_from_raw_parts_mut(bucket, size));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic() {
        let vec = AppendOnlyVec::new();
        let mut len = 0;
        assert_eq!(vec.len(), len);

        let n_buckets = 8;
        for x in 0..((1 << n_buckets) - 1) {
            let i = x as usize;
            vec.push(x);
            len += 1;
            assert_eq!(vec.len(), len);
            assert_eq!(vec.get(i), Some(&x));
        }

        assert_eq!(vec.count_buckets(), n_buckets);
        vec.push(6969);
        assert_eq!(vec.count_buckets(), n_buckets + 1);
    }
}
