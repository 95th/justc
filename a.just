while true {
    let n: int = if true {
        break
    } else {
        10
    };
}

fn fib(n: int) -> int {
    if n < 2 {
        return 1
    }  
    fib(n - 1) + fib(n - 2)
}

fn x() {
    let n = 0;
    while n < 10 {
        if n == 1 {
            break;
        }
    }
}

fn y() -> int {
    if true { return 1 } else {10}
}

fn z() -> int {
    let a = 100;
    (|| a + 100)()
}

fn t() {
    let a = 1000;
}

while true {
    let x = if true {
        break
    } else {
        continue
    };
    x + 1000;
}