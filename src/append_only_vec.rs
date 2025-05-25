use std::{
    cell::UnsafeCell,
    mem::MaybeUninit,
    ptr,
    sync::atomic::{AtomicBool, AtomicPtr, AtomicUsize, Ordering},
};

const POINTER_WIDTH: u8 = usize::BITS as u8;

/// The total number of buckets stored in each thread local.
/// All buckets combined can hold up to `2^POINTER_WIDTH - 1` entries.
const BUCKETS: usize = POINTER_WIDTH as usize;

/// Lock-free, append-only dynamic array.
pub(crate) struct AppendOnlyVec<T> {
    /// The `n`th bucket contains `2^n` elements. Each bucket is lazily allocated.
    buckets: Box<[AtomicPtr<Entry<T>>; BUCKETS]>,
    /// The total number of elements.
    ///
    /// Note that it's possible for the length to be temporarily greater than the actual number of
    /// *initialized* elements, so it should not be relied upon for `get` operations.
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

unsafe impl<T: Send> Send for AppendOnlyVec<T> {}
unsafe impl<T: Send> Sync for AppendOnlyVec<T> {}

impl<T> Default for AppendOnlyVec<T> {
    fn default() -> AppendOnlyVec<T> {
        AppendOnlyVec::new()
    }
}

impl<T> Drop for AppendOnlyVec<T> {
    fn drop(&mut self) {
        for (i, bucket) in self.buckets.iter_mut().enumerate() {
            let bucket_ptr = *bucket.get_mut();
            if bucket_ptr.is_null() {
                break;
            }
            unsafe { deallocate_bucket(bucket_ptr, bucket_size(i)) };
        }
    }
}

impl<T> AppendOnlyVec<T> {
    pub(crate) fn new() -> AppendOnlyVec<T> {
        let buckets = Box::new([const { AtomicPtr::<Entry<T>>::new(ptr::null_mut()) }; BUCKETS]);
        Self { buckets, len: AtomicUsize::new(0) }
    }

    pub(crate) fn with_capacity(capacity: usize) -> AppendOnlyVec<T> {
        let mut this = Self::new();
        let buckets = n_buckets(capacity);
        for (i, bucket) in this.buckets[..buckets].iter_mut().enumerate() {
            *bucket.get_mut() = allocate_bucket(bucket_size(i));
        }
        this
    }

    /// Returns the length of the vector.
    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.len.load(Ordering::Relaxed)
    }

    #[inline]
    pub(crate) fn push(&self, value: T) -> usize {
        let i = self.len.fetch_add(1, Ordering::AcqRel);
        let Indexes { bucket, index, bucket_size } = indexes(i);

        let bucket_atomic_ptr = unsafe { self.buckets.get_unchecked(bucket) };
        let bucket_ptr = bucket_atomic_ptr.load(Ordering::Acquire);

        // If the bucket doesn't already exist, we need to allocate it
        let bucket_ptr = if bucket_ptr.is_null() {
            Self::allocate_bucket_cold(bucket_atomic_ptr, bucket_size)
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

    #[inline(never)]
    #[cold]
    fn allocate_bucket_cold(bucket_atomic_ptr: &AtomicPtr<Entry<T>>, size: usize) -> *mut Entry<T> {
        let new_bucket = allocate_bucket(size);
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
                unsafe { deallocate_bucket(new_bucket, size) }
                bucket_ptr
            }
        }
    }

    #[inline]
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

    #[inline]
    pub(crate) unsafe fn get_unchecked(&self, index: usize) -> &T {
        #[cfg(debug_assertions)]
        {
            let len = self.len();
            assert!(index < len, "index out of bounds: the len is {len} but the index is {index}");
        }
        unsafe { self.get(index).unwrap_unchecked() }
    }

    #[cfg(test)]
    fn count_buckets(&self) -> usize {
        let n = self.buckets.iter().take_while(|b| !b.load(Ordering::Relaxed).is_null()).count();
        for bucket in &self.buckets[n..] {
            assert!(bucket.load(Ordering::Relaxed).is_null(), "discontiguous buckets");
        }
        n
    }
}

#[cfg_attr(test, derive(Debug, PartialEq, Eq))]
struct Indexes {
    bucket: usize,
    index: usize,
    bucket_size: usize,
}

#[inline]
const fn indexes(i: usize) -> Indexes {
    debug_assert!(i < usize::MAX);
    // `+ 1` to convert index to length; `- 1` to convert bucket length to bucket index.
    let bucket = n_buckets(i + 1) - 1;
    let bucket_size = bucket_size(bucket);
    let index = i - (bucket_size - 1);
    Indexes { bucket, index, bucket_size }
}

/// Returns the number of buckets needed to store `len` elements.
#[inline]
const fn n_buckets(len: usize) -> usize {
    POINTER_WIDTH as usize - len.leading_zeros() as usize
}

/// Returns the size of the bucket at the given index.
#[inline]
const fn bucket_size(bucket: usize) -> usize {
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
    let _ = Box::from_raw(ptr::slice_from_raw_parts_mut(bucket, size));
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

    #[test]
    fn correct_capacity() {
        type V = AppendOnlyVec<u32>;

        assert_eq!(V::new().count_buckets(), 0);
        assert_eq!(V::with_capacity(0).count_buckets(), 0);

        assert_eq!(V::with_capacity(1).count_buckets(), 1);

        assert_eq!(V::with_capacity(2).count_buckets(), 2);
        assert_eq!(V::with_capacity(3).count_buckets(), 2);

        assert_eq!(V::with_capacity(4).count_buckets(), 3);
        assert_eq!(V::with_capacity(5).count_buckets(), 3);
        assert_eq!(V::with_capacity(6).count_buckets(), 3);
        assert_eq!(V::with_capacity(7).count_buckets(), 3);

        assert_eq!(V::with_capacity(8).count_buckets(), 4);
    }

    #[test]
    fn non_send() {
        use std::cell::Cell;

        type V = AppendOnlyVec<Cell<u32>>;

        let v = V::new();
        assert_eq!(v.len(), 0);
        v.push(Cell::new(42));
        assert_eq!(v.len(), 1);
        assert_eq!(v.get(0).unwrap().get(), 42);
        v.get(0).unwrap().set(1);
        assert_eq!(v.get(0).unwrap().get(), 1);
    }

    #[test]
    fn test_indexes() {
        assert_eq!(indexes(0), Indexes { bucket: 0, index: 0, bucket_size: 1 });

        assert_eq!(indexes(1), Indexes { bucket: 1, index: 0, bucket_size: 2 });
        assert_eq!(indexes(2), Indexes { bucket: 1, index: 1, bucket_size: 2 });

        assert_eq!(indexes(3), Indexes { bucket: 2, index: 0, bucket_size: 4 });
        assert_eq!(indexes(4), Indexes { bucket: 2, index: 1, bucket_size: 4 });
        assert_eq!(indexes(5), Indexes { bucket: 2, index: 2, bucket_size: 4 });
        assert_eq!(indexes(6), Indexes { bucket: 2, index: 3, bucket_size: 4 });

        assert_eq!(indexes(7), Indexes { bucket: 3, index: 0, bucket_size: 8 });

        assert_eq!(indexes(usize::MAX - 1).bucket, BUCKETS - 1);
    }

    #[cfg(debug_assertions)] // TODO: Technically UB on release but it's not exposed in Interner
    #[test]
    #[should_panic]
    fn test_indexes_oob() {
        indexes(usize::MAX);
    }
}
