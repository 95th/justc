struct A { b: int }

impl A {
    fn new(b: int) -> Self {
        Self { b }
    }
}

let a = A::new(10);
a.b();