struct A { a: int }

impl A {
    fn minus(self, n: int) -> Self {
        Self { a: self.a - n }
    }
}

let a = A::minus;
a(A { a: 1 }, 1);