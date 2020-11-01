struct A { b: int }

impl A {
    fn value(self) -> int {
        self.b
    }
}

let a = A { b: 1 };
let b = 1 + a.value();