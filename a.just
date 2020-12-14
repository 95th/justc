struct X(Y);
struct Y(int);

let x = X(Y(19));
x.0.0;