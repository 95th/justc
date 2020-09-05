let a: int = {
    let b: int = 10;
    b = if b > 1 { b + 1 } else { 1 };
    b
};

a = b + 1;