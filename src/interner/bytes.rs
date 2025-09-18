use crate::{InternerSymbol, Symbol};
use boxcar::Vec as LFVec;
use bumpalo::Bump;
use dashmap::DashMap;
use hashbrown::hash_table;
use std::{collections::hash_map::RandomState, hash::BuildHasher, cell::RefCell};
use thread_local::ThreadLocal;

/// `[u8] -> Symbol` interner.
/// The hash is also stored to avoid double hashing.
///
/// This uses `NoHasher` because we want to store the `hash_builder`
/// outside of the lock, and to avoid hashing twice on insertion.
pub(crate) type Map<S> = DashMap<MapKey, S, NoHasherBuilder>;
pub(crate) type MapKey = (u64, &'static [u8]);
pub(crate) type RawMapKey<S> = (MapKey, S);

// TODO: Use a lock-free arena.
type Arena = ThreadLocal<Bump>;

/// Fast thread-local cache for recent string lookups
/// Uses 4-way set associative cache (like CPU caches) for good hit rate with minimal memory
#[derive(Debug)]
struct FastCache<S> {
    entries: [Option<CacheEntry<S>>; 4],
    next_slot: usize,
}

#[derive(Debug, Clone, Copy)]
struct CacheEntry<S> {
    hash: u64,
    len: usize,
    // Store first 8 bytes inline for fast comparison
    prefix: u64,
    symbol: S,
}

impl<S: Copy> Default for FastCache<S> {
    fn default() -> Self {
        Self {
            entries: [None; 4],
            next_slot: 0,
        }
    }
}

impl<S: Copy> FastCache<S> {
    #[inline]
    fn lookup(&self, hash: u64, s: &[u8]) -> Option<S> {
        let len = s.len();
        let prefix = Self::compute_prefix(s);

        // Check all 4 cache slots
        for entry in &self.entries {
            if let Some(cached) = entry {
                if cached.hash == hash && cached.len == len && cached.prefix == prefix {
                    return Some(cached.symbol);
                }
            }
        }
        None
    }

    #[inline]
    fn insert(&mut self, hash: u64, s: &[u8], symbol: S) {
        let entry = CacheEntry {
            hash,
            len: s.len(),
            prefix: Self::compute_prefix(s),
            symbol,
        };

        // Round-robin replacement
        self.entries[self.next_slot] = Some(entry);
        self.next_slot = (self.next_slot + 1) % 4;
    }

    #[inline]
    fn compute_prefix(s: &[u8]) -> u64 {
        // Store first 8 bytes as u64 for fast comparison
        let mut prefix = 0u64;
        let bytes_to_copy = s.len().min(8);
        for i in 0..bytes_to_copy {
            prefix |= (s[i] as u64) << (i * 8);
        }
        prefix
    }
}

thread_local! {
    static FAST_CACHE_U32: RefCell<FastCache<u32>> = RefCell::new(FastCache::default());
}

/// Byte string interner.
///
/// See the [crate-level docs][crate] for more details.
pub struct BytesInterner<S = Symbol, H = RandomState> {
    pub(crate) map: Map<S>,
    hash_builder: H,
    strs: LFVec<&'static [u8]>,
    arena: Arena,
}

impl Default for BytesInterner {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl BytesInterner<Symbol, RandomState> {
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

impl<S: InternerSymbol, H: BuildHasher> BytesInterner<S, H> {
    /// Creates a new `Interner` with the given custom hasher.
    #[inline]
    pub fn with_hasher(hash_builder: H) -> Self {
        Self::with_capacity_and_hasher(0, hash_builder)
    }

    /// Creates a new `Interner` with the given capacitiy and custom hasher.
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: H) -> Self {
        let map = Map::with_capacity_and_hasher(capacity, Default::default());
        let strs = LFVec::with_capacity(capacity);
        Self { map, strs, arena: Default::default(), hash_builder }
    }

    /// Returns the number of unique strings in the interner.
    #[inline]
    pub fn len(&self) -> usize {
        self.strs.count()
    }

    /// Returns `true` if the interner is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns an iterator over the interned strings and their corresponding `Symbol`s.
    ///
    /// Does not guarantee that it includes symbols added after the iterator was created.
    #[inline]
    pub fn iter(&self) -> impl ExactSizeIterator<Item = (S, &[u8])> + Clone {
        self.all_symbols().map(|s| (s, self.resolve(s)))
    }

    /// Returns an iterator over all symbols in the interner.
    #[inline]
    pub fn all_symbols(&self) -> impl ExactSizeIterator<Item = S> + Send + Sync + Clone {
        (0..self.len()).map(S::from_usize)
    }

    /// Interns a string, returning its unique `Symbol`.
    ///
    /// Allocates the string internally if it is not already interned.
    ///
    /// If `s` outlives `self`, like `&'static [u8]`, prefer using
    /// [`intern_static`](Self::intern_static), as it will not allocate the string on the heap.
    pub fn intern(&self, s: &[u8]) -> S {
        self.do_intern(s, alloc)
    }

    /// Interns a string, returning its unique `Symbol`.
    ///
    /// Allocates the string internally if it is not already interned.
    ///
    /// If `s` outlives `self`, like `&'static [u8]`, prefer using
    /// [`intern_mut_static`](Self::intern_mut_static), as it will not allocate the string on the
    /// heap.
    ///
    /// By taking `&mut self`, this never acquires any locks.
    pub fn intern_mut(&mut self, s: &[u8]) -> S {
        self.do_intern_mut(s, alloc)
    }

    /// Interns a static string, returning its unique `Symbol`.
    ///
    /// Note that this only requires that `s` outlives `self`, which means we can avoid allocating
    /// the string.
    pub fn intern_static<'a, 'b: 'a>(&'a self, s: &'b [u8]) -> S {
        self.do_intern(s, no_alloc)
    }

    /// Interns a static string, returning its unique `Symbol`.
    ///
    /// Note that this only requires that `s` outlives `self`, which means we can avoid allocating
    /// the string.
    ///
    /// By taking `&mut self`, this never acquires any locks.
    pub fn intern_mut_static<'a, 'b: 'a>(&'a mut self, s: &'b [u8]) -> S {
        self.do_intern_mut(s, no_alloc)
    }

    /// Interns multiple strings.
    ///
    /// Allocates the strings internally if they are not already interned.
    ///
    /// If the strings outlive `self`, like `&'static [u8]`, prefer using
    /// [`intern_many_static`](Self::intern_many_static), as it will not allocate the strings on the
    /// heap.
    pub fn intern_many<'a>(&self, strings: impl IntoIterator<Item = &'a [u8]>) {
        for s in strings {
            self.intern(s);
        }
    }

    /// Interns multiple strings.
    ///
    /// Allocates the strings internally if they are not already interned.
    ///
    /// If the strings outlive `self`, like `&'static [u8]`, prefer using
    /// [`intern_many_mut_static`](Self::intern_many_mut_static), as it will not allocate the
    /// strings on the heap.
    ///
    /// By taking `&mut self`, this never acquires any locks.
    pub fn intern_many_mut<'a>(&mut self, strings: impl IntoIterator<Item = &'a [u8]>) {
        for s in strings {
            self.intern_mut(s);
        }
    }

    /// Interns multiple static strings.
    ///
    /// Note that this only requires that the strings outlive `self`, which means we can avoid
    /// allocating the strings.
    pub fn intern_many_static<'a, 'b: 'a>(&'a self, strings: impl IntoIterator<Item = &'b [u8]>) {
        for s in strings {
            self.intern_static(s);
        }
    }

    /// Interns multiple static strings.
    ///
    /// Note that this only requires that the strings outlive `self`, which means we can avoid
    /// allocating the strings.
    ///
    /// By taking `&mut self`, this never acquires any locks.
    pub fn intern_many_mut_static<'a, 'b: 'a>(
        &'a mut self,
        strings: impl IntoIterator<Item = &'b [u8]>,
    ) {
        for s in strings {
            self.intern_mut_static(s);
        }
    }

    /// Maps a `Symbol` to its string. This is a cheap, lock-free operation.
    ///
    /// # Panics
    ///
    /// Panics if `Symbol` is out of bounds of this `Interner`. You should only use `Symbol`s
    /// created by this `Interner`.
    #[inline]
    #[must_use]
    #[cfg_attr(debug_assertions, track_caller)]
    pub fn resolve(&self, sym: S) -> &[u8] {
        if cfg!(debug_assertions) {
            self.strs.get(sym.to_usize()).expect("symbol out of bounds")
        } else {
            unsafe { self.strs.get_unchecked(sym.to_usize()) }
        }
    }

    #[inline]
    fn do_intern(&self, s: &[u8], alloc: impl FnOnce(&Arena, &[u8]) -> &'static [u8]) -> S {
        let hash = self.hash(s);

        // Fast path: Check thread-local cache first (no locks!)
        if let Some(symbol_idx) = FAST_CACHE_U32.with(|cache| cache.borrow().lookup(hash, s)) {
            return S::from_usize(symbol_idx as usize);
        }

        // Slow path: Full hash table lookup
        let shard_idx = self.map.determine_shard(hash as usize);
        let shard = &*self.map.shards()[shard_idx];

        if let Some((_, v)) = cvt(&shard.read()).find(hash, mk_eq(s)) {
            let symbol = *v.get();

            // Cache the successful lookup for next time
            FAST_CACHE_U32.with(|cache| cache.borrow_mut().insert(hash, s, symbol.to_usize() as u32));

            return symbol;
        }

        // Insert new string
        let symbol = get_or_insert(&self.strs, &self.arena, s, hash, cvt_mut(&mut shard.write()), alloc);

        // Cache the new symbol
        FAST_CACHE_U32.with(|cache| cache.borrow_mut().insert(hash, s, symbol.to_usize() as u32));

        symbol
    }

    #[inline]
    fn do_intern_mut(&mut self, s: &[u8], alloc: impl FnOnce(&Arena, &[u8]) -> &'static [u8]) -> S {
        let hash = self.hash(s);
        let shard_idx = self.map.determine_shard(hash as usize);
        let shard = &mut *self.map.shards_mut()[shard_idx];

        get_or_insert(&self.strs, &self.arena, s, hash, cvt_mut(shard.get_mut()), alloc)
    }

    #[inline]
    fn hash(&self, s: &[u8]) -> u64 {
        // We don't use `self.hash_builder.hash_one(s)` because we want to avoid hashing the length.
        use std::hash::Hasher;
        let mut h = self.hash_builder.build_hasher();
        h.write(s);
        h.finish()
    }
}

pub(crate) type NoHasherBuilder = std::hash::BuildHasherDefault<NoHasher>;

pub(crate) enum NoHasher {}
impl Default for NoHasher {
    #[inline]
    fn default() -> Self {
        unreachable!()
    }
}
impl std::hash::Hasher for NoHasher {
    #[inline]
    fn finish(&self) -> u64 {
        match *self {}
    }
    #[inline]
    fn write(&mut self, _bytes: &[u8]) {
        match *self {}
    }
}

#[inline]
fn get_or_insert<S: InternerSymbol>(
    strs: &LFVec<&'static [u8]>,
    arena: &Arena,
    s: &[u8],
    hash: u64,
    shard: &mut hash_table::HashTable<RawMapKey<dashmap::SharedValue<S>>>,
    alloc: impl FnOnce(&Arena, &[u8]) -> &'static [u8],
) -> S {
    match shard.entry(hash, mk_eq(s), hasher) {
        hash_table::Entry::Occupied(e) => *e.get().1.get(),
        hash_table::Entry::Vacant(e) => {
            let s = alloc(arena, s);
            let i = strs.push(s);
            let new_sym = S::from_usize(i);
            e.insert(((hash, s), dashmap::SharedValue::new(new_sym)));
            new_sym
        }
    }
}

#[inline]
fn hasher<S>(((hash, _), _): &RawMapKey<S>) -> u64 {
    *hash
}

#[inline]
fn mk_eq<S>(s: &[u8]) -> impl Fn(&RawMapKey<S>) -> bool + Copy + '_ {
    let len = s.len();
    move |((_, ss), _): &RawMapKey<S>| {
        let other = *ss;
        // Fast length check first - avoids expensive byte comparison
        len == other.len() && s == other
    }
}

#[inline]
fn alloc(arena: &Arena, s: &[u8]) -> &'static [u8] {
    // SAFETY: extends the lifetime of `&Arena` to `'static`. This is never exposed so it's ok.
    unsafe {
        std::mem::transmute::<&[u8], &'static [u8]>(arena.get_or_default().alloc_slice_copy(s))
    }
}

#[inline]
fn no_alloc(_: &Arena, s: &[u8]) -> &'static [u8] {
    // SAFETY: `s` outlives `arena`, so we don't need to allocate it. See above.
    unsafe { std::mem::transmute::<&[u8], &'static [u8]>(s) }
}

// SAFETY: `HashTable` is a thin wrapper around `RawTable`. This is not guaranteed but idc.
#[inline]
fn cvt<T>(old: &hashbrown::raw::RawTable<T>) -> &hash_table::HashTable<T> {
    unsafe { std::mem::transmute(old) }
}

#[inline]
fn cvt_mut<T>(old: &mut hashbrown::raw::RawTable<T>) -> &mut hash_table::HashTable<T> {
    unsafe { std::mem::transmute(old) }
}
