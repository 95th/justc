struct A { a: int }
impl A {
    fn one() -> Self {
        Self { a: 1 }
    }

    fn minus(self, n: int) -> Self {
        Self { a: self.a - n }
    }

    fn less_than(self, n: int) -> bool {
        self.a < n
    }

    fn add(self, other: Self) -> Self {
        Self { a: self.a + other.a }
    }
}

fn fib(a: A) -> A {
    if a.less_than(2) {
        A::one()
    } else {
        let a = a.minus(1).a;
        let b = a.minus(2);
        let a = fib(a);
        let b = fib(b);
        a.add(b)
    }
}