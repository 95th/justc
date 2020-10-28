struct A { a: int }
let f = |a, b, c: fn(A, A) -> int| c(a, b);

let t = A { a: 1 };
f(t, t, |a, b| a.a + b.a);