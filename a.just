struct B { a: int }
impl B {
    fn minus(self, n: int) -> Self {
        Self { a: self.a - n }
    }
}

let a = B::minus;
a(B { a: 1 }, 1); 
bar(B::minus);

fn bar(f: fn(B, int) -> B) {}

if a + a {
    
}