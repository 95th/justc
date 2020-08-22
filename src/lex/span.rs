#[derive(Debug, Default, Copy, Clone)]
pub struct Span {
    lo: usize,
    hi: usize,
}

impl Span {
    pub const DUMMY: Span = Span::new(0, 0);

    pub const fn new(lo: usize, hi: usize) -> Self {
        Self { lo, hi }
    }

    pub const fn lo(&self) -> usize {
        self.lo
    }

    pub const fn hi(&self) -> usize {
        self.hi
    }
}

#[derive(Debug, Default, Copy, Clone)]
pub struct Spanned<T> {
    pub node: T,
    pub span: Span,
}
