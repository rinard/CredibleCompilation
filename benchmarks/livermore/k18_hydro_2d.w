var j : int, k : int, rep : int, idx : int;
array za[1024] : float, zp[1024] : float, zr[1024] : float;

k := 0;
while (k < 1024) {
  zp[k] := intToFloat(k) * 0.01;
  zr[k] := intToFloat(k) * 0.005 + 0.5;
  za[k] := 0.0;
  k := k + 1
};

rep := 0;
while (rep < 10000) {
  j := 1;
  while (j < 31) {
    k := 1;
    while (k < 31) {
      idx := j * 32 + k;
      za[idx] := (zp[idx + 1] - zp[idx - 1]) * zr[idx]
               + (zp[idx + 32] - zp[idx - 32]) * zr[idx];
      k := k + 1
    };
    j := j + 1
  };
  rep := rep + 1
}
