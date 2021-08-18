# Scoped-Arena

[![crates](https://img.shields.io/crates/v/scoped-arena.svg?style=for-the-badge&label=scoped-arena)](https://crates.io/crates/scoped-arena)
[![docs](https://img.shields.io/badge/docs.rs-scoped-arena-66c2a5?style=for-the-badge&labelColor=555555&logoColor=white)](https://docs.rs/scoped-arena)
[![actions](https://img.shields.io/github/workflow/status/zakarumych/scoped-arena/badge/master?style=for-the-badge)](https://github.com/zakarumych/scoped-arena/actions?query=workflow%3ARust)
[![MIT/Apache](https://img.shields.io/badge/license-MIT%2FApache-blue.svg?style=for-the-badge)](COPYING)
![loc](https://img.shields.io/tokei/lines/github/zakarumych/scoped-arena?style=for-the-badge)


Scoped-Arena provides arena-like allocator with optional scopes.
Arena allocators are simple and provides ludicrously fast allocation.

`Scope` allows storing values. When dropped `Scope` will `Drop` all stored values and free memory allocated by the scope.\
Well placed scopes can significantly reduce memory consumption.\
Creating new scope is cheap and allocating within scope is as fast as allocating parent arena allocator.\
Drop glue is stored in scope only for values that `needs_drop`. i.e. for `Copy` types storing value on scope is simply allocation + copy.\

Rust borrowing rules require additional layer of `ScopeProxy` to allow references to values on scope and sub-scopes to coexist.

## License

Licensed under either of

* Apache License, Version 2.0, ([license/APACHE](license/APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
* MIT license ([license/MIT](license/MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contributions

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.
