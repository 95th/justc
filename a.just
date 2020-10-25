struct A {
    a: int,
}

fn foo(a: A, f: fn(A) -> fn(A) -> int) -> int {
    f(a)(a)
}