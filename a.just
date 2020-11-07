struct Fibonnacci {
    n: int
}

impl Fibonnacci {
    fn new(n: int) -> Self {
        Self { n }
    }

    fn calc(self) -> int {
        self.calc_inner(self.n)
    }

    fn calc_inner(self, n: int) -> int {
        if n < 2 {
            1
        } else {
            self.calc_inner(n - 1) + self.calc_inner(n - 2)
        }
    }
}

let fib = Fibonnacci::new(10);
fib.calc();
let f = Fibonnacci::calc(fib);