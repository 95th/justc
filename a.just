struct A {}

impl A {
    fn add() -> Self { Self {} }
}

let a = A::add();
a.add();