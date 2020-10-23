fn fib(a: int) -> int {
    if a >= 2 {
        fib(a - 1) + fib(a - 2)
    } else {
        let c = |a| {
            return 1;
        };
        (c)(1)
    }
}

fib(10);