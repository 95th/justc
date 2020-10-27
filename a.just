struct A { a: int }
let f = |a: A, b: A| a.a + b.a;
f(A {a: 1}, A{b: 1});