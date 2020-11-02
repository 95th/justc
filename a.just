struct A { n: int }

impl A {
    fn new(n: int) -> Self {
        Self { n }
    }

    fn fib(self) -> int {
        if self.n < 2 {
            1
        } else {
            Self::new(self.n - 1).fib() + Self::new(self.n - 2).fib()
        }
    }
}