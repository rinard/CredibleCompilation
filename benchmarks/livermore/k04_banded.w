var k : int, rep : int, xk : float,
    fuzz : float, buzz : float, fizz : float;
array x[1001] : float, y[1001] : float;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 0;
while (k < 1001) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  x[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 0;
while (k < 1001) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  y[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

rep := 0;
while (rep < 10000) {
  k := 5;
  while (k < 1001) {
    xk := x[k];
    x[k - 4] := x[k - 4] - xk * y[k - 4];
    x[k - 3] := x[k - 3] - xk * y[k - 3];
    x[k - 2] := x[k - 2] - xk * y[k - 2];
    x[k - 1] := x[k - 1] - xk * y[k - 1];
    x[k]     := x[k]     - xk * y[k];
    k := k + 5
  };
  rep := rep + 1
}
