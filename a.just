struct B { a: int }

impl B {
    fn foo(self, n: int) {
        self.a = self.a + n;
    }
}

fn foo(b: B) {
    impl B {
        fn foo(self) {
            self.a = self.a + n;
        }
    }

    b.foo();
}

fn foo() {}