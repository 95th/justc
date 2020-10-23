fn fib(a: int) -> int {
    if a >= 2 {
        fib(a - 1) + fib(a - 2)
    } else {
        return;
    }
}

fib(10);