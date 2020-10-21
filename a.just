{
    fn fib(a: int) -> int {
        if a < 2 { 1 } else { fib(a - 1) + fib(a - 2) }
    }

    fib(1);
}