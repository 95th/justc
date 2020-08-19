fn foo(i: (i32, u32, abc::def::Ghi)) {
    print i;
}

for i in 0..=100 {
    foo(i);
}