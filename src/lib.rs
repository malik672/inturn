#![doc = include_str!("../README.md")]
#![cfg_attr(not(test), warn(unused_crate_dependencies))]
#![cfg_attr(docsrs, feature(doc_cfg, doc_auto_cfg))]

use bumpalo::Bump;
use dashmap::{DashMap, RwLock};
use std::{collections::hash_map::RandomState, hash::BuildHasher, num::NonZeroU32};

/// Default unique identifier for a string in an [`Interner`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Symbol(NonZeroU32);

impl Symbol {
    /// Creates a new `Symbol` from a `u32`.
    ///
    /// # Panics
    ///
    /// Panics if `id` is `u32::MAX`.
    #[inline]
    pub fn new(id: u32) -> Self {
        Self::try_new(id).unwrap()
    }

    /// Tries to create a new `Symbol` from a `u32`.
    #[inline]
    pub fn try_new(id: u32) -> Option<Self> {
        if id < u32::MAX {
            // SAFETY: `id` is less than `u32::MAX`.
            Some(unsafe { Self::new_unchecked(id) })
        } else {
            None
        }
    }

    /// Creates a new `Symbol` from a `usize`.
    ///
    /// # Panics
    ///
    /// Panics if `id` is greater than or equal to `u32::MAX`.
    #[inline]
    pub fn from_usize(id: usize) -> Self {
        Self::try_from_usize(id).unwrap()
    }

    /// Tries to create a new `Symbol` from a `usize`.
    #[inline]
    pub fn try_from_usize(id: usize) -> Option<Self> {
        if id < u32::MAX as usize {
            // SAFETY: `id` is less than `u32::MAX`.
            Some(unsafe { Self::new_unchecked(id as u32) })
        } else {
            None
        }
    }

    /// Creates a new `Symbol` from a `u32` without checking if it is valid.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `id` is less than `u32::MAX`.
    #[inline]
    pub unsafe fn new_unchecked(id: u32) -> Self {
        Self(unsafe { NonZeroU32::new_unchecked(id.unchecked_add(1)) })
    }

    /// Returns the `u32` value of the `Symbol`.
    #[inline]
    pub fn get(self) -> u32 {
        // SAFETY: `NonZeroU32` is guaranteed to be non-zero, so we can safely
        // subtract 1 to get the original id.
        unsafe { self.0.get().unchecked_sub(1) }
    }

    /// Returns the `usize` value of the `Symbol`.
    #[inline]
    pub fn to_usize(self) -> usize {
        self.get() as usize
    }
}

/// Trait for types that can be used as symbols in an `Interner`.
pub trait InternerSymbol: Sized + Copy + std::hash::Hash + Eq {
    /// Tries to create a new `Symbol` from a `usize`.
    fn try_from_usize(id: usize) -> Option<Self>;

    /// Converts the `Symbol` to a `usize`.
    fn to_usize(self) -> usize;
}

impl InternerSymbol for Symbol {
    #[inline]
    fn try_from_usize(id: usize) -> Option<Self> {
        Self::try_from_usize(id)
    }

    #[inline]
    fn to_usize(self) -> usize {
        self.to_usize()
    }
}

/// `str -> Symbol` interner.
/// The hash is also stored to avoid double hashing.
///
/// This uses `NoHasher` because we want to store the `hash_builder`
/// outside of the lock, and to avoid hashing twice on insertion.
type Map<S> = DashMap<MapKey, S, NoHasherBuilder>;
type MapKey = (u64, &'static str);
type RawMapKey<S> = (MapKey, S);

/// String interner.
///
/// See the [module docs][self] for more details.
pub struct Interner<S = Symbol, H = RandomState> {
    map: Map<S>,
    inner: RwLock<Inner>,
    hash_builder: H,
}

struct Inner {
    strs: Vec<&'static str>,
    arena: Bump,
}

// SAFETY: `Bump` is only used when we have exclusive write access to `Inner`.
unsafe impl Sync for Inner {}

impl Default for Interner {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl Interner<Symbol, RandomState> {
    /// Creates a new, empty `Interner` with the default symbol and hasher.
    #[inline]
    pub fn new() -> Self {
        Self::with_capacity(0)
    }

    /// Creates a new `Interner` with the given capacity and default symbol and hasher.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, Default::default())
    }
}

impl<S: InternerSymbol, H: BuildHasher> Interner<S, H> {
    /// Creates a new `Interner` with the given custom hasher.
    #[inline]
    pub fn with_hasher(hash_builder: H) -> Self {
        Self::with_capacity_and_hasher(0, hash_builder)
    }

    /// Creates a new `Interner` with the given capacitiy and custom hasher.
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: H) -> Self {
        let map = Map::with_capacity_and_hasher(capacity, Default::default());
        let strs = Vec::with_capacity(capacity);
        Self { map, inner: RwLock::new(Inner { strs, arena: Bump::new() }), hash_builder }
    }

    /// Returns the number of unique strings in the interner.
    #[inline]
    pub fn len(&self) -> usize {
        self.inner.read().strs.len()
    }

    /// Returns `true` if the interner is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Interns a string, returning its unique `Symbol`.
    ///
    /// Allocates the string internally if it is not already interned.
    ///
    /// If `s` outlives `self`, like `&'static str`, prefer using
    /// [`intern_static`](Self::intern_static), as it will not allocate the string on the heap.
    #[inline]
    pub fn intern(&self, s: &str) -> S {
        self.do_intern(s, alloc)
    }

    /// Interns a string, returning its unique `Symbol`.
    ///
    /// Allocates the string internally if it is not already interned.
    ///
    /// If `s` outlives `self`, like `&'static str`, prefer using
    /// [`intern_mut_static`](Self::intern_mut_static), as it will not allocate the string on the
    /// heap.
    ///
    /// By taking `&mut self`, this never acquires any locks.
    #[inline]
    pub fn intern_mut(&mut self, s: &str) -> S {
        self.do_intern_mut(s, alloc)
    }

    /// Interns a static string, returning its unique `Symbol`.
    ///
    /// Note that this only requires that `s` outlives `self`, which means we can avoid allocating
    /// the string.
    #[inline]
    pub fn intern_static<'a, 'b: 'a>(&'a self, s: &'b str) -> S {
        self.do_intern(s, no_alloc)
    }

    /// Interns a static string, returning its unique `Symbol`.
    ///
    /// Note that this only requires that `s` outlives `self`, which means we can avoid allocating
    /// the string.
    ///
    /// By taking `&mut self`, this never acquires any locks.
    #[inline]
    pub fn intern_mut_static<'a, 'b: 'a>(&'a mut self, s: &'b str) -> S {
        self.do_intern_mut(s, no_alloc)
    }

    /// Maps a `Symbol` to its string.
    ///
    /// # Panics
    ///
    /// Panics if `Symbol` is out of bounds of this `Interner`. You should only use `Symbol`s
    /// created by this `Interner`.
    #[inline]
    pub fn resolve(&self, sym: S) -> &str {
        unsafe { self.inner.read().strs.get_unchecked(sym.to_usize()) }
    }

    #[inline]
    fn do_intern(&self, s: &str, alloc: impl FnOnce(&mut Bump, &str) -> &'static str) -> S {
        let hash = self.hash(s);
        let shard_idx = self.map.determine_shard(hash as usize);
        let shard = &*self.map.shards()[shard_idx];
        let eq = mk_eq(s);

        if let Some((_, sym)) = shard.read().find(hash, eq) {
            return *sym;
        }

        let shard = &mut *shard.write();
        match shard.entry(hash, eq, hasher) {
            hashbrown::hash_table::Entry::Occupied(e) => e.get().1,
            hashbrown::hash_table::Entry::Vacant(e) => {
                insert_vacant(&mut self.inner.write(), s, hash, e, alloc)
            }
        }
    }

    #[inline]
    fn do_intern_mut(&mut self, s: &str, alloc: impl FnOnce(&mut Bump, &str) -> &'static str) -> S {
        let hash = self.hash(s);
        let shard_idx = self.map.determine_shard(hash as usize);
        let shard = &mut *self.map.shards_mut()[shard_idx];
        match shard.get_mut().entry(hash, mk_eq(s), hasher) {
            hashbrown::hash_table::Entry::Occupied(e) => e.get().1,
            hashbrown::hash_table::Entry::Vacant(e) => {
                insert_vacant(self.inner.get_mut(), s, hash, e, alloc)
            }
        }
    }

    #[inline]
    fn hash(&self, s: &str) -> u64 {
        self.hash_builder.hash_one(s)
    }
}

type NoHasherBuilder = std::hash::BuildHasherDefault<NoHasher>;

#[derive(Default)]
struct NoHasher;
impl std::hash::Hasher for NoHasher {
    fn finish(&self) -> u64 {
        unimplemented!()
    }
    fn write(&mut self, _bytes: &[u8]) {
        unimplemented!()
    }
}

#[inline]
fn insert_vacant<S: InternerSymbol>(
    inner: &mut Inner,
    s: &str,
    hash: u64,
    e: hashbrown::hash_table::VacantEntry<'_, RawMapKey<S>>,
    alloc: impl FnOnce(&mut Bump, &str) -> &'static str,
) -> S {
    let s = alloc(&mut inner.arena, s);
    let new_sym = S::try_from_usize(inner.strs.len()).expect("ran out of symbols");
    inner.strs.push(s);
    e.insert(((hash, s), new_sym));
    new_sym
}

#[inline]
fn hasher<S>(((hash, _), _): &RawMapKey<S>) -> u64 {
    *hash
}

#[inline]
fn mk_eq<S>(s: &str) -> impl Fn(&RawMapKey<S>) -> bool + Copy + '_ {
    move |((_, ss), _): &RawMapKey<S>| s == *ss
}

#[inline]
fn alloc(arena: &mut Bump, s: &str) -> &'static str {
    // SAFETY: extends the lifetime of `&mut Bump` to `'static`. This is never exposed so it's ok.
    unsafe { std::mem::transmute::<&str, &'static str>(arena.alloc_str(s)) }
}

#[inline]
fn no_alloc(_: &mut Bump, s: &str) -> &'static str {
    // SAFETY: `s` outlives `Bump`, so we don't need to allocate it. See above.
    unsafe { std::mem::transmute::<&str, &'static str>(s) }
}

#[cfg(test)]
mod tests {
    use super::*;

    const fn _assert_send_sync<T: Send + Sync>() {}
    const _: () = _assert_send_sync::<Interner>();

    macro_rules! basic {
        ($intern:ident) => {
            #[allow(unused_mut)]
            let mut interner = Interner::new();
            assert!(interner.map.is_empty());

            let hello = interner.$intern("hello");
            assert_eq!(hello.get(), 0);
            assert_eq!(interner.resolve(hello), "hello");
            assert_eq!(interner.len(), 1);

            let world = interner.$intern("world");
            assert_eq!(world.get(), 1);
            assert_eq!(interner.resolve(world), "world");
            assert_eq!(interner.len(), 2);

            let hello2 = interner.$intern("hello");
            assert_eq!(hello, hello2);
            let hello3 = interner.$intern("hello");
            assert_eq!(hello, hello3);

            let world2 = interner.$intern("world");
            assert_eq!(world, world2);

            assert_eq!(interner.len(), 2);

            #[allow(unused_mut)]
            let mut interner2 = Interner::new();
            let prefill = &["hello", "world"];
            for &s in prefill {
                interner2.$intern(s);
            }
            assert_eq!(interner2.resolve(hello), "hello");
            assert_eq!(interner2.resolve(world), "world");
            assert_eq!(interner2.$intern("hello"), hello);
            assert_eq!(interner2.$intern("world"), world);
            assert_eq!(interner2.len(), 2);
        };
    }

    #[test]
    fn basic() {
        basic!(intern);
    }
    #[test]
    fn basic_mut() {
        basic!(intern_mut);
    }
    #[test]
    fn basic_static() {
        basic!(intern_static);
    }
    #[test]
    fn basic_mut_static() {
        basic!(intern_mut_static);
    }

    #[test]
    #[cfg_attr(miri, ignore = "too slow")]
    fn mt() {
        let interner = Interner::new();
        let symbols_per_thread = 5000;
        let n_threads = std::thread::available_parallelism().map(|x| x.get()).unwrap_or(4);

        std::thread::scope(|scope| {
            let intern_many = |salt: usize| {
                let intern_one = |i: usize| {
                    let s = format!("hello {salt} {i}");
                    let sym = interner.intern(&s);
                    assert_eq!(interner.resolve(sym), s);
                };
                for i in 0..symbols_per_thread {
                    intern_one(i);
                    intern_one(i);
                }
            };
            for i in 0..n_threads {
                scope.spawn(move || intern_many(i));
            }
        });

        assert_eq!(interner.len(), n_threads * symbols_per_thread);
    }

    #[test]
    fn hash_collision() {
        #[derive(Default)]
        struct MyBadHasher;
        impl std::hash::Hasher for MyBadHasher {
            fn finish(&self) -> u64 {
                4 // Chosen by fair dice roll.
            }
            fn write(&mut self, _bytes: &[u8]) {}
        }

        let interner = Interner::<Symbol, _>::with_hasher(std::hash::BuildHasherDefault::<
            MyBadHasher,
        >::default());
        let hello = interner.intern("hello");
        let world = interner.intern("world");
        assert_eq!(hello.get(), 0);
        assert_eq!(world.get(), 1);
        assert_eq!(interner.resolve(hello), "hello");
        assert_eq!(interner.resolve(world), "world");
        assert_eq!(interner.len(), 2);
    }
}
