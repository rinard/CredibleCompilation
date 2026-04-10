var k : int, m : int, rep : int, xm : float, xk : float,
    fuzz : float, buzz : float, fizz : float;
array x[1001] : float;

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

rep := 0;
while (rep < 10000) {
  x[500] := 0.0 - 10000000000.0;
  m := 0;
  xm := x[0];
  k := 1;
  while (k < 1001) {
    xk := x[k];
    if (xk < xm) {
      m := k;
      xm := xk
    } else {
      skip
    };
    k := k + 1
  };
  rep := rep + 1
}
