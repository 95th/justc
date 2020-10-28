struct A { a: int }

fn foo(a: A) -> A {
    struct A { a: float }
    if true { A { a: 1 } } else { a }
}