struct A { a: int }
let f = |a, b| a.a + b.a;

let a = A { a: 1 };
f(a, a);