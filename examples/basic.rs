use scoped_arena::Arena;

#[derive(Debug, PartialEq, Eq)]
struct Foo(u32);

impl Drop for Foo {
    fn drop(&mut self) {
        println!("Drop Foo at {:p} with {}", self, self.0);
    }
}

fn main() {
    // Creating the arena.
    let mut arena = Arena::new();

    // Creating root scope.
    let mut scope = arena.scope();
    let mut proxy = scope.proxy();

    let value_in_root_scope = proxy.to_scope(Foo(42));

    for i in 0..3 {
        // Creating sub-scope that inherits arena and uses same bucket allocator,
        // but drops values moved to the sub-scope,
        // and frees memory allocated for them,
        // keeping values on parent scope intact.
        let scope = proxy.scope();

        // Move value with `Drop` onto scope.
        let value_in_scope = scope.to_scope(Foo(i));

        // Ensure that value is moved properly.
        assert_eq!(value_in_scope.0, i);

        // Ensure that value in root scope is not affected.
        assert_eq!(value_in_root_scope.0, 42);
    }

    drop(proxy);
    let slice = scope.to_scope_from_iter([Foo(100), Foo(101)]);

    assert_eq!(slice, &[Foo(100), Foo(101)]);

    drop(scope);

    println!("Total memory usage: {} bytes", arena.total_memory_usage());
}
