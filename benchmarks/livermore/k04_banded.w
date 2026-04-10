var k : int, j : int, lw : int, m : int, rep : int, temp : float,
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
  m := (1001 - 7) / 2;
  k := 6;
  while (k < 1001) {
    lw := k - 6;
    temp := x[k - 1];
    j := 4;
    while (j < 1001) {
      if (lw < 1001) {
        temp := temp - x[lw] * y[j]
      } else { skip };
      lw := lw + 1;
      j := j + 5
    };
    x[k - 1] := y[4] * temp;
    k := k + m
  };
  rep := rep + 1
}
