# Scoped-Arena

[![crates](https://img.shields.io/crates/v/scoped-arena.svg?style=for-the-badge&label=scoped-arena)](https://crates.io/crates/scoped-arena)
[![docs](https://img.shields.io/badge/docs.rs-scoped--arena-66c2a5?style=for-the-badge&labelColor=555555&logoColor=white)](https://docs.rs/scoped-arena)
[![actions](https://img.shields.io/github/workflow/status/zakarumych/scoped-arena/badge/master?style=for-the-badge)](https://github.com/zakarumych/scoped-arena/actions?query=workflow%3ARust)
[![MIT/Apache](https://img.shields.io/badge/license-MIT%2FApache-blue.svg?style=for-the-badge)](COPYING)
![loc](https://img.shields.io/tokei/lines/github/zakarumych/scoped-arena?style=for-the-badge)

Scoped-Arena provides arena allocator with explicit scopes.

## Arena allocation

Arena allocators are simple and provides ludicrously fast allocation.\
Basically allocation requires only increment of internal pointer in the memory block to alignment of allocated object and then to size of allocated object and that's it.\
When memory block is exhausted arena will allocate new bigger memory block.\
Then arena can be reset after all allocated objects are not used anymore, keeping only last memory block and reuse it.\
After several warmup iterations the only memory block is large enough to handle all allocations until next reset.


### Example

```rust
use scoped_arena::Scope;

struct Cat {
    name: String,
    hungry: bool,
}

/// Create new arena with `Global` allocator.
let mut scope = Scope::new();

/// Construct a cat and move it to the scope.
let cat: &mut Cat = scope.to_scope(Cat {
    name: "Fluffy".to_owned(),
    hungry: true,
});

// Now `cat` is a mutable reference bound to scope borrow lifetime.

assert_eq!(&cat.name, "Fluffy");
assert!(cat.hungry);

cat.hungry = false;

// This cat instance on scope will be automatically dropped when `scope` is dropped or reset.
// It is impossible to reset before last usage of `cat`.

// Next line will drop cat value and free memory occupied by it.
scope.reset();

// If there were more cats or any other objects put on scope they all would be dropped and memory freed.
```

## Scopes

To reuse memory earlier this crates provides `Scope` with methods to create sub-`Scope`s.\
When sub-`Scope` is reset or dropped it will `Drop` all stored values and free memory allocated by the scope and flush last of new allocated memory block into parent.\
While objects allocated with parent `Scope` are unchanged and still valid.

Well placed scopes can significantly reduce memory consumption.\
For example if few function calls use a lot of dynamic memory but don't need it to be available in caller\
they can be provided with sub-scope.\
At the same time any memory allocated in parent scope stays allocated.

Creating sub-scope is cheap and allocating within sub-scope is as fast as allocating in parent scope.\

### Example

```rust
use scoped_arena::{Scope, ScopeProxy};


fn heavy_on_memory(mut scope: Scope<'_>, foobar: &String) {
    for _ in 0 .. 42 {
        let foobar: &mut String = scope.to_scope(foobar.clone());
    }

    // new `scope` is dropped here and drops all allocated strings and frees memory.
}

let mut scope = Scope::new();

// Proxy is required to be friends with borrow checker.
// Creating sub-scope must lock parent `Scope` from being used, which requires mutable borrow, but any allocation borrows `Scope`.
// `Proxy` relaxes this a bit. `Proxy` borrows `Scope` mutably and tie allocated objects lifetime to scopes' borrow lifetime.
// So sub-scope can borrow proxy mutably while there are objects allocated from it.
let mut proxy = scope.proxy();

let foobar: &mut String = proxy.to_scope("foobar".to_owned());

// Make sub-scope for the call.
heavy_on_memory(proxy.scope(), &*foobar);

// If `heavy_on_memory` didn't trigger new memory object allocation in the scope,
// sub-scope drop would rewind scope's internals to exactly the same state.
// Otherwise last of new blocks will become current block in parent scope.
//
// Note that `foobar` is still alive.

heavy_on_memory(proxy.scope(), &*foobar);
heavy_on_memory(proxy.scope(), &*foobar);
heavy_on_memory(proxy.scope(), &*foobar);
heavy_on_memory(proxy.scope(), &*foobar);

// Once peak memory consumption is reached, any number of `heavy_on_memory` calls would not require new memory blocks to be allocated.
// Even `loop { heavy_on_memory(proxy.scope(), &*foobar) }` will settle on some big enough block.
```

## Dropping

`to_scope` and `try_to_scope` methods store drop-glue for values that `needs_drop`.
On reset or drop scope iterates and properly drops all values.
No drop-glue is added for types that doesn't need drop. `Scope` allocates enough memory and writes value there, no bookkeeping overhead.

## Iterator collecting

`to_scope_from_iter` method acts as `to_scope` but works on iterators and returns slices.
The limitation is that `to_scope_from_iter` need to allocate memory enough for upper bound of what iterator can yield.
If upper bound is too large or iterator is unbounded it will always fail.
One can use `try_to_scope_from_iter` so fail is `Err` and not panic.
It is safe for iterator to yield more items then upper bound it reports, `to_scope_from_iter` would not iterate past upper bound.
On success it returns mutable reference to slice with items from iterator in order.
All values will be dropped on scope reset or drop, same as with `to_scope`.

This method is especially useful to deal with API that requires slices (*glares at FFI*), collecting into temporary `Vec` would cost much more.

## #![no_std] Support

Scoped-Arena is a no_std crate. It depends only core crates and optionally on `alloc` crate.

## Nightly Rust feature(allocator_api) Support

Scoped-Arena uses copy of `allocator_api` traits and types for underlying allocator.\
On nightly channel it is possible to enable `allocator_api` feature for this crate. Then actual `allocator_api` traits and types will be used instead,
enabling using any compatible allocator.
Additionally it `&Arena`, `&Scope` and `ScopeProxy` will implement `core::alloc::Allocator` making them suitable for standard rust collections.

Note that as rust `allocator_api` feature is unstable, this crate's `allocator_api` feature is also considered unstable and may not follow semver.
That is, changes to follow `allocator_api` modifications in rust can be published with patch version, although they must not break code that does not use the feature.

## License

Licensed under either of

* Apache License, Version 2.0, ([license/APACHE](license/APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
* MIT license ([license/MIT](license/MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contributions

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.
