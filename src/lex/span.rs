use std::{fmt, ops::Range};

#[derive(Default, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Span {
    lo: usize,
    hi: usize,
}

impl fmt::Debug for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}..{})", self.lo, self.hi)
    }
}

impl Span {
    pub const DUMMY: Span = Span::new(0, 0);

    pub const fn new(lo: usize, hi: usize) -> Self {
        Self { lo, hi }
    }

    pub fn lo(&self) -> usize {
        self.lo
    }

    pub fn hi(&self) -> usize {
        self.hi
    }

    pub fn to(self, other: Span) -> Self {
        Self {
            lo: self.lo.min(other.lo),
            hi: self.hi.max(other.hi),
        }
    }
}

impl From<Range<usize>> for Span {
    fn from(r: Range<usize>) -> Self {
        Self::new(r.start, r.end)
    }
}

#[derive(Copy, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Spanned<T> {
    pub val: T,
    pub span: Span,
}

impl<T: fmt::Debug> fmt::Debug for Spanned<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}@{:?}", self.val, self.span)
    }
}

impl<T> Spanned<T> {
    pub fn new(val: T, span: Span) -> Self {
        Self { val, span }
    }
}
