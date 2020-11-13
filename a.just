fn foo(f: fn(int) -> bool) -> bool {
    f(100)
}

foo(|n| n = 0)