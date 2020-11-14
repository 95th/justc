fn fact(n: int) -> int {
    let out = 0;
    while n > 0 {
        out *= n;
        n -= 1;
    }
    out
}

fact(1000);
call(fact);

fn call(f: fn(int) -> int) -> int {
    f(100)
}