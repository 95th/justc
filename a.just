let a: (((int, int), str), float) = (((1, 1), "hello"), 2.0);

let f: fn(int, float) -> str = |a: int, b: float| ("hello", 1).0;

fn f2(x: (int, float)) {}

f2((1, 2));