var k : int, rep : int, expx : float, s : float,
    fuzz : float, buzz : float, fizz : float;
array x[1001] : float, y[1001] : float;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 0;
while (k < 1001) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  x[k] := (buzz - fizz) * 0.1 + 0.01;
  k := k + 1
};

s := 0.0;

rep := 0;
while (rep < 10000) {
  k := 0;
  while (k < 1001) {
    expx := exp(x[k]);
    y[k] := x[k] / (expx - 1.0);
    k := k + 1
  };
  rep := rep + 1
};

s := y[0]
