struct X { a: int }

impl X {
    fn value(self) -> Self {
        Self { a: self.a + 1 }
    }
}