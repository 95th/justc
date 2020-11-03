struct A { a: int }

impl A {
    fn minus(self, n: int) -> Self {
        Self { a: self.a - n }
    }
}

foo(A::minus);

fn foo(f: fn(A, int) -> A) {}