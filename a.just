{
    fn fib(n: int) -> int {
        if n < 2 { 1 } else { fib(n - 1) + fib(n - 2) }
    }

    fib(100);
}