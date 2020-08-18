fn foo(i: i32) {
    print i;
}

let i: i32 = 100;
for i in 0..=100 {
    foo(i);
}