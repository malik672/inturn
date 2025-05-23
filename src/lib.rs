//! Efficient, thread-safe string interner.
//!
//! # Examples
//!
//! ```
//! use the_interner::Interner;
//!
//! let interner = Interner::new();
//! let hello = interner.intern("hello");
//! assert_eq!(hello.get(), 0);
//! assert_eq!(interner.resolve(hello), "hello");
//!
//! let world = interner.intern("world");
//! assert_eq!(world.get(), 1);
//! assert_eq!(interner.resolve(world), "world");
//!
//! let hello2 = interner.intern("hello");
//! assert_eq!(hello, hello2);
//!
//! assert_eq!(interner.len(), 2);
//! ```

#![cfg_attr(not(test), warn(unused_crate_dependencies))]
#![cfg_attr(docsrs, feature(doc_cfg, doc_auto_cfg))]

use bumpalo::Bump;
use dashmap::{DashMap, RwLock};
use std::{
    hash::{BuildHasher, RandomState},
    num::NonZeroU32,
};

mod no_hash;
use no_hash::NoHasherBuilder;

/// Unique identifier for a string in an [`Interner`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Symbol(NonZeroU32);

impl Symbol {
    /// Creates a new `Symbol` from a `u32`.
    #[inline]
    pub fn new(id: u32) -> Self {
        Self(NonZeroU32::new(id.wrapping_add(1)).unwrap())
    }

    /// Creates a new `Symbol` from a `usize`.
    #[inline]
    pub fn from_usize(id: usize) -> Self {
        Self::new(id as u32)
    }

    /// Returns the `u32` value of the `Symbol`.
    #[inline]
    pub fn get(self) -> u32 {
        self.0.get().wrapping_sub(1)
    }

    /// Returns the `usize` value of the `Symbol`.
    #[inline]
    pub fn get_usize(self) -> usize {
        self.get() as usize
    }
}

/// `str -> Symbol` interner.
/// The `str` is stored in `strs` instead of in the map to avoid double hashing.
///
/// This uses `NoHasher` because we want to store the `hash_builder`
/// outside of the lock, and to avoid hashing twice on insertion.
type Map = DashMap<u64, Symbol, NoHasherBuilder>;
type MapKey = (u64, Symbol);

/// String interner.
///
/// See the [module docs][self] for more details.
pub struct Interner<S = RandomState> {
    map: Map,
    inner: RwLock<Inner>,
    hash_builder: S,
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

impl Interner {
    /// Creates a new, empty `Interner`.
    #[inline]
    pub fn new() -> Self {
        Self::with_capacity(0)
    }

    /// Creates a new `Interner` with the given capacity.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, Default::default())
    }
}

impl<S: BuildHasher> Interner<S> {
    /// Creates a new `Interner` with the given custom hasher.
    pub fn with_hasher(hash_builder: S) -> Self {
        Self::with_capacity_and_hasher(0, hash_builder)
    }

    /// Creates a new `Interner` with the given capacitiy and custom hasher.
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
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
    pub fn intern(&self, s: &str) -> Symbol {
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
    pub fn intern_mut(&mut self, s: &str) -> Symbol {
        self.do_intern_mut(s, alloc)
    }

    /// Interns a static string, returning its unique `Symbol`.
    ///
    /// Note that this only requires that `s` outlives `self`, which means we can avoid allocating
    /// the string.
    #[inline]
    pub fn intern_static<'a, 'b: 'a>(&'a self, s: &'b str) -> Symbol {
        self.do_intern(s, no_alloc)
    }

    /// Interns a static string, returning its unique `Symbol`.
    ///
    /// Note that this only requires that `s` outlives `self`, which means we can avoid allocating
    /// the string.
    ///
    /// By taking `&mut self`, this never acquires any locks.
    #[inline]
    pub fn intern_mut_static<'a, 'b: 'a>(&'a mut self, s: &'b str) -> Symbol {
        self.do_intern_mut(s, no_alloc)
    }

    /// Maps a `Symbol` to its string.
    #[inline]
    pub fn resolve(&self, sym: Symbol) -> &str {
        self.inner.read().strs[sym.get() as usize]
    }

    #[inline]
    fn do_intern<'a>(
        &self,
        s: &'a str,
        alloc: impl FnOnce(&'a str, &mut Bump) -> &'static str,
    ) -> Symbol {
        let hash = self.hash(s);
        let shard_idx = self.map.determine_shard(hash as usize);
        let shard = &*self.map.shards()[shard_idx];
        let eq = mk_eq(hash);

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
    fn do_intern_mut<'a>(
        &mut self,
        s: &'a str,
        alloc: impl FnOnce(&'a str, &mut Bump) -> &'static str,
    ) -> Symbol {
        let hash = self.hash(s);
        let shard_idx = self.map.determine_shard(hash as usize);
        let shard = &mut *self.map.shards_mut()[shard_idx];
        match shard.get_mut().entry(hash, mk_eq(hash), hasher) {
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

#[inline]
fn insert_vacant<'a>(
    inner: &mut Inner,
    s: &'a str,
    hash: u64,
    e: hashbrown::hash_table::VacantEntry<'_, MapKey>,
    alloc: impl FnOnce(&'a str, &mut Bump) -> &'static str,
) -> Symbol {
    let s = alloc(s, &mut inner.arena);
    let new_sym = Symbol::from_usize(inner.strs.len());
    inner.strs.push(s);
    e.insert((hash, new_sym));
    new_sym
}

#[inline]
fn hasher((hash, _): &MapKey) -> u64 {
    *hash
}

#[inline]
fn mk_eq(hash: u64) -> impl Fn(&MapKey) -> bool + Copy {
    move |(h, _): &MapKey| *h == hash
}

#[inline]
fn alloc(s: &str, arena: &mut Bump) -> &'static str {
    // SAFETY: extends the lifetime of `&mut Bump` to `'static`. This is never exposed so it's ok.
    unsafe { std::mem::transmute::<&str, &'static str>(arena.alloc_str(s)) }
}

#[inline]
fn no_alloc(s: &str, _: &mut Bump) -> &'static str {
    // SAFETY: `s` outlives `bump`, so we don't need to allocate it. See above.
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
            assert_eq!(interner.map.len(), 1);

            let world = interner.$intern("world");
            assert_eq!(world.get(), 1);
            assert_eq!(interner.resolve(world), "world");
            assert_eq!(interner.map.len(), 2);

            let hello2 = interner.$intern("hello");
            assert_eq!(hello, hello2);
            let hello3 = interner.$intern("hello");
            assert_eq!(hello, hello3);

            let world2 = interner.$intern("world");
            assert_eq!(world, world2);

            assert_eq!(interner.map.len(), 2);

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
            assert_eq!(interner2.map.len(), 2);
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

        assert_eq!(interner.map.len(), n_threads * symbols_per_thread);
    }
}
