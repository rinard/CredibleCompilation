var j : int, k : int, rep : int, qa : float;
array za[707] : float, zr[707] : float, zb[707] : float, zu[707] : float, zv[707] : float, zz[707] : float;

k := 0;
while (k < 707) {
  za[k] := intToFloat(k) * 0.002;
  zr[k] := intToFloat(k) * 0.003 + 0.1;
  zb[k] := intToFloat(k) * 0.001 + 0.2;
  zu[k] := intToFloat(k) * 0.004 + 0.3;
  zv[k] := intToFloat(k) * 0.005 + 0.4;
  zz[k] := intToFloat(k) * 0.006 + 0.5;
  k := k + 1
};

rep := 0;
while (rep < 100000) {
  j := 1;
  while (j < 6) {
    k := 1;
    while (k < 100) {
      qa := za[j + 1 + (k * 7)] * zr[j + (k * 7)] + za[j - 1 + (k * 7)] * zb[j + (k * 7)]
          + za[j + ((k + 1) * 7)] * zu[j + (k * 7)] + za[j + ((k - 1) * 7)] * zv[j + (k * 7)] + zz[j + (k * 7)];
      za[j + (k * 7)] := za[j + (k * 7)] + 0.175 * (qa - za[j + (k * 7)]);
      k := k + 1
    };
    j := j + 1
  };
  rep := rep + 1
}
