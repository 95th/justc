fn foo(f: (fn(), fn() -> (int))) -> int {
    f.1()
}