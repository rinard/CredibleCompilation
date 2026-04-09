var k : int, rep : int, dk : float, s : float, t : float, di : float, dn : float;
array y[1024] : float, g[1024] : float, xx[1024] : float, z[1024] : float, w[1024] : float, v[1024] : float, u[1024] : float, vv[1024] : float, x[1024] : float;

k := 0;
while (k < 1024) {
  y[k]  := intToFloat(k) * 0.01 + 1.0;
  g[k]  := intToFloat(k) * 0.005;
  xx[k] := intToFloat(k) * 0.02 + 0.5;
  z[k]  := intToFloat(k) * 0.003;
  w[k]  := intToFloat(k) * 0.001 + 0.1;
  v[k]  := intToFloat(k) * 0.004;
  u[k]  := intToFloat(k) * 0.002 + 0.3;
  vv[k] := intToFloat(k) * 0.006 + 1.0;
  k := k + 1
};

dk := 1.5;
s  := 0.001;
t  := 100.0;

rep := 0;
while (rep < 10000) {
  k := 0;
  while (k < 1024) {
    di := y[k] - g[k] / (xx[k] + dk);
    dn := 0.0;
    if (di < 0.0 - 0.0001) {
      dn := z[k] / di;
      if (dn > t) { dn := t } else { skip };
      if (dn < s) { dn := s } else { skip }
    } else {
      if (di > 0.0001) {
        dn := z[k] / di;
        if (dn > t) { dn := t } else { skip };
        if (dn < s) { dn := s } else { skip }
      } else {
        skip
      }
    };
    x[k] := ((w[k] + v[k] * dn) * xx[k] + u[k]) / (vv[k] + v[k] * dn);
    k := k + 1
  };
  rep := rep + 1
}
