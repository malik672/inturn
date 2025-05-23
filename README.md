# the-interner

Efficient, thread-safe string interner.

## Examples

```rust
use the_interner::Interner;

let interner = Interner::new();
let hello = interner.intern("hello");
assert_eq!(hello.get(), 0);
assert_eq!(interner.resolve(hello), "hello");

let world = interner.intern("world");
assert_eq!(world.get(), 1);
assert_eq!(interner.resolve(world), "world");

let hello2 = interner.intern("hello");
assert_eq!(hello, hello2);

assert_eq!(interner.len(), 2);
```
