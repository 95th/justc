struct A {
    a: int,
}

let a: fn(A, A) -> int = |a, b| a.a + b.a;

// fn foo(a: A, b: A) -> int {
//     a.a + b.a
// }