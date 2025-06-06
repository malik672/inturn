#![doc = include_str!("../README.md")]
#![cfg_attr(not(test), warn(unused_crate_dependencies))]
#![cfg_attr(docsrs, feature(doc_cfg, doc_auto_cfg))]

mod interner;
pub use interner::Interner;

mod symbol;
pub use symbol::{InternerSymbol, Symbol};

mod lock_free_stack;
