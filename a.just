struct X { a: int }

impl X {
    fn add_one(a: int, self) -> Self {
        Self { a: self.a + 1 }
    }
}
