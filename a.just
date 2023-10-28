struct Foo<T> {
    bar: Bar<T, float>
}

struct Bar<T, U> {
    value: T,
    other: U
}

let foo = Foo {
    bar: Bar {
        value: 42,
        other: 1.2
    }
};

let f: Bar<_, _> = Bar {
    value: 42,
    other: 1.2
};

f.value == 2;