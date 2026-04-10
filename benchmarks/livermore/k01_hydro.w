var q : float, r : float, t : float, k : int, rep : int,
    fuzz : float, buzz : float, fizz : float;
array x[1001] : float, y[1001] : float, z[1001] : float;

q := 0.1;
r := 0.1;
t := 0.1;

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

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 0;
while (k < 1001) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  z[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

rep := 0;
while (rep < 10000) {
  k := 0;
  while (k < 990) {
    x[k] := q + y[k] * (r * z[k + 10] + t * z[k + 11]);
    k := k + 1
  };
  rep := rep + 1
}
