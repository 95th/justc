struct A {
    n: int,
}

impl A {
    fn f(self) -> int {
        self.n
    }
}

struct B {
    a: A
}

struct C {
    b: B
}

let c = C { b: B { a: A { n: 10 } } };
let x = c.b.a.f() + 1.0;