use justc::Compiler;

use std::sync::Once;

/// Setup function that is only run once, even if called multiple times.
fn setup() {
    static INIT: Once = Once::new();
    INIT.call_once(|| env_logger::init());
}

fn run_ok(src: &str) {
    setup();
    let src = String::from(src);
    let mut c = Compiler::new();
    c.run(src).unwrap();
}

fn run_err(src: &str) {
    setup();
    let src = String::from(src);
    let mut c = Compiler::new();
    c.run(src).unwrap_err();
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

#[test]
fn wrong_type_simple() {
    run_err(
        r#"
        let a: int = 1.0;
    "#,
    );
}

#[test]
fn wrong_type_partial() {
    run_err(
        r#"
        let a: (int, int) = (1, 2.0);
    "#,
    );
}

#[test]
fn wrong_type_same_name() {
    run_err(
        r#"
        struct X { a: int }
        fn foo() -> X {
            struct X { a: int }
            X { a: 1 }
        }
    "#,
    );
}

#[test]
fn wrong_loop_return_type() {
    run_err(
        r#"
        fn foo() {
            loop {
                break 10;
            }
        }
    "#,
    );
}

#[test]
fn array_creation() {
    run_ok(
        r#"
        let a: [int] = [];
        let a = [1];
        let a = [1,];
        let a = [1, 2];
        let a = [1, 2, ];
        let a = [1; 2];
        let a = [1; a[0]];
        let a = [true; 2];
        let a = [(1, 2); 2];
    "#,
    );
}

#[test]
fn generic_struct_single_use() {
    run_ok(
        r#"
        struct S<T>(T);
        let a = S(1);
        a.0 == 1;
    "#,
    );
}

#[test]
fn generic_struct_multi_use() {
    run_ok(
        r#"
        struct S<T>(T);
        let a = S(1);
        let b = S(true);
        a.0 == 1;
        b.0 == true;
    "#,
    );
}

#[test]
fn generic_args() {
    run_ok(
        r#"
        struct Foo<T>(Bar<T>);
        struct Bar<T>(T);
    "#,
    );
}

#[test]
fn generic_arg_infer() {
    run_ok(
        r#"
        struct Foo<T>(T);
        let f: Foo<_> = Foo(20);
        f.0 == 20;
    "#,
    )
}

#[test]
fn generic_function() {
    run_ok(
        r#"
        fn foo<T>(a: T) -> T {
            a
        }

        let a = foo(10);
        let b = foo(1.1);
    "#,
    )
}
