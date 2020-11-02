struct B { a: int }

impl B {
    fn foo(self, n: int) {
        self.a = self.a + n;
    }
}

fn x() {
    impl B {
        fn bar(self) {
            self.a = self.a + 1;
        }
    }
}

fn y() {}