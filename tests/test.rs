use justc::Compiler;

fn run_ok(src: &str) {
    let src = String::from(src);
    let mut c = Compiler::new();
    c.run(src).unwrap();
}

#[test]
fn binary() {
    run_ok(
        r#"
        let a = 10;
        let b = 20;
        a + b;
    "#,
    );
}

#[test]
fn binary_assign() {
    run_ok(
        r#"
        let a = 10;
        let b = 20;
        a += b;
    "#,
    );
}

#[test]
fn array() {
    run_ok(
        r#"
        let a = [1, 2, 3];
        a[1] = 1;
        a[2] += 1;
    "#,
    );
}

#[test]
fn loop_infinite() {
    run_ok(
        r#"
        let a: int = loop {};
    "#,
    );
}

#[test]
fn loop_break() {
    run_ok(
        r#"
        let a: int = loop {
            if true {
                break 10;
            }
        };
    "#,
    );
}

#[test]
fn loop_break_return_in_fn() {
    run_ok(
        r#"
        fn foo() {
            let a: int = loop {
                if true {
                    break 10;
                } else {
                    return;
                }
            };
        }
    "#,
    );
}

#[test]
fn struct_expr_and_field_access() {
    run_ok(
        r#"
        struct X { a: int }
        let x = X { a: 1 };
        let a: int = x.a;
    "#,
    );
}

#[test]
fn tuple_struct_expr_and_field_access() {
    run_ok(
        r#"
        struct X(int);
        let x = X(1);
        let a: int = x.0;
    "#,
    );
}

#[test]
fn tuple_return_and_access() {
    run_ok(
        r#"
        fn foo() -> (int, float) {
            (1, 2.0)
        }
        let a: (int, float) = foo();
        let x: int = foo().0;
        let x: float = foo().1;
    "#,
    );
}

#[test]
fn closure_expr_and_call() {
    run_ok(
        r#"
        let f = || (1, 2.0);
        let a: (int, float) = f();
    "#,
    );
}
