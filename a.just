struct A {x:int}

impl A {
    fn add(self, val: int) {
        self.x = self.x + val;
    }
}

let a = A { x: 1 };
a.add(2);