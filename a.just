let a = |a, b| a(b);
let b = a(|a| a > 1, 2);
let b = a(|a| a < 1, 2);