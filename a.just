struct Int {a: int}

impl Int {
    fn set_value(self, val: int) {
        self.a = val;
    }

    fn value(self) -> int {
        self.a
    }

    fn replace(self, val: Int) -> Int {
        let tmp = self;
        self = val;
        tmp
    }
}