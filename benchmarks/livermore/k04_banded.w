var k : int, rep : int, xk : float;
array x[1024] : float, y[1024] : float;

k := 0;
while (k < 1024) {
  x[k] := intToFloat(k) * 0.01 + 1.0;
  y[k] := intToFloat(k) * 0.001;
  k := k + 1
};

rep := 0;
while (rep < 10000) {
  k := 5;
  while (k < 1024) {
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
