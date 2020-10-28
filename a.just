struct A { a: int }
struct B {
    a: A,
    b: fn(int) -> int,
}

let b = B {
    a: A { a: 1 },
    b: |a| a + 1,
};

b.b();