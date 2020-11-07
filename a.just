struct A { b: int, minus: fn(int) -> A }

impl A {
    fn new(b: int) -> Self {
        Self { b, minus: A::new }
    }

    fn minus(self, n: int) -> Self {
        Self {
            b: self.b - n,
            minus: self.minus
        }
    }
}

let a = A::new(10);
(a.minus)(1);
a.minus(1);
A::minus(a, 1);
let f = A::minus;
f(a, 1);


foo(A::minus);
foo(|a, n| a);
foo(|a, n| A { b: a.b + n, minus: A::new });

fn foo(f: fn(A, int) -> A) { }
