pub(crate) type NoHasherBuilder = std::hash::BuildHasherDefault<NoHasher>;

#[derive(Default)]
pub(crate) struct NoHasher(u64);
impl std::hash::Hasher for NoHasher {
    #[inline]
    fn finish(&self) -> u64 {
        self.0
    }

    #[inline]
    fn write(&mut self, _bytes: &[u8]) {
        unimplemented!()
    }

    #[inline]
    fn write_u64(&mut self, i: u64) {
        self.0 = i;
    }
}
