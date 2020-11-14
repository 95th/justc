fn foo(n: int) {
    while n < 10000 {
        n -= 1;
        foo(n);
        if n + 1 == 2 {
            break
        } else if n > 1000 {
            return;
        } else {
            continue
        }
    }
}