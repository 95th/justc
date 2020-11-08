struct A {}

impl A {
    fn new() -> Self { Self {} }
}

let a = A::new;
a();