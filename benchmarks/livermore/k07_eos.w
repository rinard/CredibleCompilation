var k : int, rep : int, r : float, t : float, q : float;
array x[1001] : float, y[1001] : float, z[1001] : float, u[1001] : float;

k := 0;
while (k < 1001) {
  y[k] := intToFloat(k) * 0.01;
  z[k] := intToFloat(k) * 0.02 + 1.0;
  u[k] := intToFloat(k) * 0.003 + 0.5;
  k := k + 1
};

r := 0.5;
t := 0.3;
q := 0.2;

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
