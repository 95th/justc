fn is_odd(a: int, x: bool) -> bool {
    if a == 1 {
        true
    } else {
        is_even(a - 1, x)
    }
}

fn is_even(a: int, x: bool) -> bool {
    if a == 0 {
        true
    } else {
        return is_odd(a - 1, x);
    }
}
