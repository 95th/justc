fn foo(a: fn((int, bool)) -> int) {}

foo(|a| if a.1 { a.0 } else { 1 });