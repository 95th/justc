struct A { a: int }

fn bar() -> A {
    struct A { a: float }
   
    fn foo() -> A {
        if true { A { a: 1.0 } } else { A { a: 1.0 } }
    }

    foo()
}