struct A { a: int }
let f = |a: A, b| a.a + b.a;
f(A {a: 1}, A{b: 1});