fn fib(n: int) -> int  {
    if n < 2 {
        return 1;
    }

    let f1 = fib(n - 1);
    let f2 = fib(n - 2);
    f1 + f2
}

fn foo(n: int) -> int {
    let out = 0;
    loop {
        if n == 0 {
            break out;
        }

        let x = fib(n);
        out += x;
        n -= 1;
    }
}