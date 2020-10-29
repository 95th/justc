struct X { a: int }

impl X {
    fn add_one(self, a: Self) -> Self {
        struct A {
            a: Self
        }
        Self { a: self.a + 1 }
    }
}
