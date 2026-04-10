var k : int, rep : int, expmax : float,
    fuzz : float, buzz : float, fizz : float;
array u[101] : float, v[101] : float, x[101] : float,
      y[101] : float, w[101] : float;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 0;
while (k < 101) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  u[k] := (buzz - fizz) * 0.1 + 0.01;
  k := k + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 0;
while (k < 101) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  v[k] := (buzz - fizz) * 0.1 + 0.01;
  k := k + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 0;
while (k < 101) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  x[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

expmax := 20.0;

rep := 0;
while (rep < 10000) {
  u[100] := 0.99 * expmax * v[100];
  k := 0;
  while (k < 101) {
    y[k] := u[k] / v[k];
    w[k] := x[k] / (exp(y[k]) - 1.0);
    k := k + 1
  };
  rep := rep + 1
};

expmax := w[0]
