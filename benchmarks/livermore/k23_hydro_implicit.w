var j : int, k : int, rep : int, qa : float,
    fuzz : float, buzz : float, fizz : float;
array za[707] : float, zr[707] : float, zb[707] : float, zu[707] : float, zv[707] : float, zz[707] : float;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 0;
while (k < 707) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  za[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 0;
while (k < 707) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  zr[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 0;
while (k < 707) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  zb[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 0;
while (k < 707) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  zu[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 0;
while (k < 707) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  zv[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 0;
while (k < 707) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  zz[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

k := 0;
while (k < 707) {
  zr[k] := zr[k] * 0.1;
  zb[k] := zb[k] * 0.1;
  zu[k] := zu[k] * 0.1;
  zv[k] := zv[k] * 0.1;
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
