struct X {a: int}

let x = X {a:1};
x.a = 10;

let f = || X {a:1};
f().a = 20;

fn foo() -> X { X {a:1} }
foo().a = 30;

(x.a) = X{a:2}.a;