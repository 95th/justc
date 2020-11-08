struct A { n: int }

impl A {
    fn new(n: int) -> Self {
        Self { n }
    }
}

let a: fn(A) -> int = |a| a.n + 1;