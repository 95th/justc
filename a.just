struct X { a: int }

impl X {
    fn add_one(self) -> Self {
        Self { a: self.a + 1 }
    }
}
