struct A { a: int }
let f = |a: A, b: A, c: fn(A, A) -> int| c(a, b);

let a = A { a: 1 };
f(a, a, |a: A, b: A| a.a + b.a);