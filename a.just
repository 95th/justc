struct Foo<T>(T);

let a = Foo(10);
let b = Foo(1.0);
let c = Foo(20);
a.0 == c.0;
a = c;