fn fib(a: int) -> int {
    if a >= 2 {
        fib(a - 1) + fib(a - 2)
    } else {
        fn x(a: int) -> bool {
            return a > 1;
        }
        if x(a) { 1 } else {
            return false;
        }
    }
}

fib(10);