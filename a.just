let a = |a, b| {
    a(b + 1)
};

let a = || {
    if a(|a| a + 1, 1) > 1 {
        return 1;
    }

    return 0;
};