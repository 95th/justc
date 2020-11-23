struct Range {
    lo: int,
    hi: int,
}

impl Range {
    fn new(lo: int, hi: int) -> Self {
        Self { lo, hi }
    }

    fn zero() -> Self {
        Self::new(0, 0)
    }
}

let r = Range::new(1, 2);
r.lo + r.hi