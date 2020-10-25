struct A {
    a: int,
}

let a: fn(A, A) -> int = |a, b| a.a + b.a;
