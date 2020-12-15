fn t() {
	let a: int = if true { 1 } else { return; };
    return;
    if true { true } else { false };
}


fn t2() -> int {
	let a: int = if true { 1 } else { return 1; };
    return 1;
    if true { () } else {  }
    1
}

let a: int = loop {
    break 10;
};