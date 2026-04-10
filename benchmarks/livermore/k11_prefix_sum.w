var i : int, rep : int,
    fuzz : float, buzz : float, fizz : float;
array x[1001] : float, y[1001] : float;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
i := 0;
while (i < 1001) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  y[i] := (buzz - fizz) * 0.1;
  i := i + 1
};

rep := 0;
while (rep < 10000) {
  x[0] := y[0];
  i := 1;
  while (i < 1001) {
    x[i] := x[i - 1] + y[i];
    i := i + 1
  };
  rep := rep + 1
}
