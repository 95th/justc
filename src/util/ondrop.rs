use std::ops::{Deref, DerefMut};

pub struct OnDrop<'a, T, F: FnMut(&mut T)> {
    val: &'a mut T,
    f: F,
}

impl<'a, T, F: FnMut(&mut T)> OnDrop<'a, T, F> {
    pub fn new(val: &'a mut T, f: F) -> Self {
        Self { val, f }
    }
}

impl<T, F: FnMut(&mut T)> Deref for OnDrop<'_, T, F> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.val
    }
}

impl<T, F: FnMut(&mut T)> DerefMut for OnDrop<'_, T, F> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.val
    }
}

impl<T, F: FnMut(&mut T)> Drop for OnDrop<'_, T, F> {
    fn drop(&mut self) {
        (self.f)(self.val)
    }
}
