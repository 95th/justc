enum Foo {
    A,
    B { a: int, b: float },
    C(int, float),
}

let a = Foo::B { a: 1, b: 10 };