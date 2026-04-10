var i : int, rep : int, q : float,
    fuzz : float, buzz : float, fizz : float;
array x[1001] : float, z[1001] : float;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
i := 0;
while (i < 1001) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  x[i] := (buzz - fizz) * 0.1;
  i := i + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
i := 0;
while (i < 1001) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  z[i] := (buzz - fizz) * 0.1;
  i := i + 1
};

rep := 0;
while (rep < 10000) {
  q := 0.0;
  i := 0;
  while (i < 1001) {
    q := q + x[i] * z[i];
    i := i + 1
  };
  rep := rep + 1
}
