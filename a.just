struct A { a: int }

impl A {
    fn new() -> A {
        A { a: 1 }
    }

    fn int_value(self) -> int {
        self.a
    }
}