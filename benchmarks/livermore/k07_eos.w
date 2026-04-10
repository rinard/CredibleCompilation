var k : int, rep : int, r : float, t : float, q : float,
    fuzz : float, buzz : float, fizz : float;
array x[1001] : float, y[1001] : float, z[1001] : float, u[1001] : float;

r := 0.1;
t := 0.1;
q := 0.1;

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

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 0;
while (k < 1001) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  u[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

rep := 0;
while (rep < 10000) {
  k := 0;
  while (k < 995) {
    x[k] := u[k] + r * (z[k] + r * y[k])
           + t * (u[k + 3] + r * (u[k + 2] + r * u[k + 1])
           + t * (u[k + 6] + q * (u[k + 5] + q * u[k + 4])));
    k := k + 1
  };
  rep := rep + 1
}
