struct A {
    a: int,
}

let f = |a, b| a.a + b.a;
f(A {a:1}, A{a:1})