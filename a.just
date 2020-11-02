struct A { x: int }

impl A {
    fn new() -> Self {
        Self { x: 1 }
    }

    fn add(self, val: int) {
        self.x = self.x + val;
    }
}

let a = A::new();
a.add(2);
A::add(a, 2);
