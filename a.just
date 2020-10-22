fn fib(a: int) -> int {
    let fib = 10;
    if a >= 2 { fib(a - 1) + fib(a - 2) } else { 1 }
}

{
    fn fib2(a: int) {
        fib(a)
    }
    fib2(10);
}