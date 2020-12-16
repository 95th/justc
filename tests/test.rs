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

