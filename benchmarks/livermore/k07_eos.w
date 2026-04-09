var k : int, rep : int, r : float;
array x[1024] : float, y[1024] : float, z[1024] : float, u[1024] : float;

k := 0;
while (k < 1024) {
  y[k] := intToFloat(k) * 0.01;
  z[k] := intToFloat(k) * 0.02 + 1.0;
  u[k] := intToFloat(k) * 0.003 + 0.5;
  k := k + 1
};

r := 0.5;

rep := 0;
while (rep < 10000) {
  k := 0;
  while (k < 1024) {
    x[k] := u[k] + r * (z[k] + r * y[k]);
    k := k + 1
  };
  rep := rep + 1
}
