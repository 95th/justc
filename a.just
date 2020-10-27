struct A { a: int }
fn f(a:A, b:A) -> int {
    a.a + b.a
}

let a = A { a: 1 };
f(a, a);