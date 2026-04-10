var k : int, rep : int, dk : float, s : float, t : float, di : float, dn : float,
    fuzz : float, buzz : float, fizz : float;
array y[1000] : float, g[1000] : float, xx[1001] : float, z[1000] : float,
      w[1000] : float, v[1000] : float, u[1000] : float, vx[1000] : float,
      x[1000] : float;

dk := 0.1;
s  := 0.1;
t  := 0.1;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 0;
while (k < 1000) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  y[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 0;
while (k < 1000) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  g[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 0;
while (k < 1000) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  z[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 0;
while (k < 1000) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  w[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 0;
while (k < 1000) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  v[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 0;
while (k < 1000) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  u[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 0;
while (k < 1000) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  vx[k] := (buzz - fizz) * 0.1 + 2.0;
  k := k + 1
};

rep := 0;
while (rep < 10000) {
  k := 0;
  while (k < 1000) {
    di := y[k] - g[k] / (xx[k] + dk);
    dn := 0.2;
    if (di < 0.0) {
      dn := z[k] / di;
      if (t < dn) { dn := t } else { skip };
      if (s > dn) { dn := s } else { skip }
    } else {
      if (di > 0.0) {
        dn := z[k] / di;
        if (t < dn) { dn := t } else { skip };
        if (s > dn) { dn := s } else { skip }
      } else {
        skip
      }
    };
    x[k] := ((w[k] + v[k] * dn) * xx[k] + u[k]) / (vx[k] + v[k] * dn);
    xx[k + 1] := (x[k] - xx[k]) * dn + xx[k];
    k := k + 1
  };
  rep := rep + 1
}
