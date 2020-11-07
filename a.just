struct Fibonnacci {
    n: int
}

impl Fibonnacci {
    fn new(n: int) -> Self {
        Self { n }
    }

    fn calc(self) -> int {
        calc_fib(self.n)
    }
}

fn calc_fib(n: int) -> int {
    if n < 2 {
        1
    } else {
        calc_fib(n - 1) + calc_fib(n - 2)
    }
}

let fib = Fibonnacci::new(10);
fib.calc();
let f = Fibonnacci::calc(fib);