struct A { b: int }

impl A {
    fn new(b: int) -> Self {
        Self { b }
    }

    fn minus(self, n: int) -> Self {
        Self {
            b: self.b - n
        }
    }
}

let a = A::new(10);
a.fib();

foo(A::minus);
foo(|a, n| a);
foo(|a, n| A { b: a.b + n });

fn foo(f: fn(A, int) -> A) { }
