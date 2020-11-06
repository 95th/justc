struct A { b: B }
struct B { a: fn() -> A }

impl A {
    fn new() -> Self {
        Self {
            b: B {
                a: Self::new,
            }
        }
    }
}

fn foo() -> fn() -> A {
    A::new
}