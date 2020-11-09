struct A {}

impl A {
    fn foo() {
        fn bar() -> Self {
            Self {}
        }
    }
}