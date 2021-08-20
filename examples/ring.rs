use scoped_arena::Scope;

struct Foo(&'static str);

impl Drop for Foo {
    fn drop(&mut self) {
        print!("{}", self.0);
    }
}

fn use_scopes(a: &mut Scope, b: &mut Scope, c: &mut Scope) {
    a.to_scope(Foo("a"));
    b.to_scope(Foo("b"));
    c.to_scope(Foo("c"));
}

fn main() {
    let mut scope_a = Scope::new();
    let mut scope_b = Scope::new();
    let mut scope_c = Scope::new();

    for i in 0..10 {
        match i % 3 {
            0 => {
                scope_a.reset();
                use_scopes(&mut scope_a, &mut scope_b, &mut scope_c)
            }
            1 => {
                scope_b.reset();
                use_scopes(&mut scope_b, &mut scope_c, &mut scope_a)
            }
            2 => {
                scope_c.reset();
                use_scopes(&mut scope_c, &mut scope_a, &mut scope_b)
            }
            _ => {}
        }
    }
}
