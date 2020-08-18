let a = 0;

while a < 1000 {
    a = a + 1;

    if a % 2 != 0 {
        continue;
    }

    print a;

    if a > 100 {
        break;
    }
}