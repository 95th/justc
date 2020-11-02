struct A { n: int }

impl A {
    fn new(n: int) -> Self {
        Self { n }
    }

    fn fib(self) -> int {
        if self.n < 2 {
            1
        } else {
            let b = B { a: 1 };
            b.foo(1);
            Self::new(self.n - 1).fib() + Self::new(self.n - 2).fib()
        }
    }
}

let x = B { a: 1 };

struct B { a: int }
impl B {
    fn foo(self, n: int) {
        self.a = self.a + n;
    }
}