struct A { a: int }

impl A {
    fn foo(self, a: fn() -> Self, b: (Self, Self)) -> Self {
        self
    }
}
