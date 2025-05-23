use bumpalo::Bump;
use indexmap::IndexMap;
use std::hash::{BuildHasher, RandomState};
use std::num::NonZeroU32;
use std::sync::{PoisonError, RwLock};

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

/// String interner.
pub struct Interner<S = RandomState> {
    inner: RwLock<Inner>,
    hash_builder: S,
}

struct Inner {
    // This is `NoHasher` because we want to store the `hash_builder`
    // outside of the lock to avoid hashing twice on insertion.
    map: IndexMap<u64, &'static str, NoHasherBuilder>,
    arena: Bump,
}

// SAFETY: not safe
unsafe impl Sync for Inner {}

impl Inner {
    fn new(prefill: &[&'static str], hash_builder: &impl BuildHasher) -> Self {
        let mut map = IndexMap::with_capacity_and_hasher(prefill.len(), Default::default());
        for &s in prefill {
            map.insert(hash_builder.hash_one(s), s);
        }
        Self {
            map,
            arena: Bump::new(),
        }
    }
}

impl Interner {
    /// Creates a new, empty `Interner`.
    #[inline]
    pub fn new() -> Self {
        Self::prefilled(&[])
    }

    /// Creates a new `Interner` with prefilled strings.
    #[inline]
    pub fn prefilled(prefill: &[&'static str]) -> Self {
        Self::prefilled_with_hasher(prefill, Default::default())
    }
}

impl<S: BuildHasher> Interner<S> {
    /// Creates a new `Interner` with prefilled strings and a custom hasher.
    #[inline]
    pub fn prefilled_with_hasher(prefill: &[&'static str], hash_builder: S) -> Self {
        Self {
            inner: RwLock::new(Inner::new(prefill, &hash_builder)),
            hash_builder,
        }
    }

    /// Interns a string, returning its unique `Symbol`.
    ///
    /// Allocates the string internally if it is not already interned.
    #[inline]
    pub fn intern(&self, s: &str) -> Symbol {
        self.do_intern(s, |s, inner| {
            let s = &*inner.arena.alloc_str(s);
            // SAFETY: `s` is valid for the lifetime of `self`.
            // We use `'static` to get around being self-referential.
            unsafe { std::mem::transmute::<&str, &'static str>(s) }
        })
    }

    /// Interns a static string, returning its unique `Symbol`.
    ///
    /// Does not allocate the string.
    #[inline]
    pub fn intern_static(&self, s: &'static str) -> Symbol {
        self.do_intern(s, |s, _| s)
    }

    /// Maps a `Symbol` back to its string representation.
    #[inline]
    pub fn resolve(&self, sym: Symbol) -> &str {
        *self.read().map.get_index(sym.get() as usize).unwrap().1
    }

    #[inline]
    fn do_intern<'a>(
        &self,
        s: &'a str,
        alloc: impl FnOnce(&'a str, &mut Inner) -> &'static str,
    ) -> Symbol {
        let hash = self.hash(s);
        if let Some(sym) = self.get(hash) {
            return sym;
        }

        let inner = &mut *self.write();
        let new_id = inner.map.len();
        let s = alloc(s, inner);
        let id = if let (idx, Some(prev)) = inner.map.insert_full(hash, s) {
            debug_assert_eq!(prev, s, "inconsistent intern");
            idx
        } else {
            new_id
        };
        Symbol::from_usize(id)
    }

    #[inline]
    fn read(&self) -> impl std::ops::Deref<Target = Inner> + '_ {
        self.inner.read().unwrap_or_else(PoisonError::into_inner)
    }

    #[inline]
    fn write(&self) -> impl std::ops::DerefMut<Target = Inner> + '_ {
        self.inner.write().unwrap_or_else(PoisonError::into_inner)
    }

    #[inline]
    fn get(&self, s: u64) -> Option<Symbol> {
        let inner = &*self.read();
        inner.map.get_index_of(&s).map(Symbol::from_usize)
    }

    #[inline]
    fn hash(&self, s: &str) -> u64 {
        self.hash_builder.hash_one(s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_send_sync<T: Send + Sync>() {}

    #[test]
    fn test() {
        assert_send_sync::<Interner>();

        let interner = Interner::new();
        let hello = interner.intern("hello");
        assert_eq!(hello.get(), 0);
        assert_eq!(interner.resolve(hello), "hello");

        let world = interner.intern("world");
        assert_eq!(world.get(), 1);
        assert_eq!(interner.resolve(world), "world");

        let hello2 = interner.intern("hello");
        assert_eq!(hello, hello2);
        let hello3 = interner.intern("hello");
        assert_eq!(hello, hello3);

        let world2 = interner.intern("world");
        assert_eq!(world, world2);
    }
}
