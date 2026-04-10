var j : int, k : int, rep : int, idx : int, qa : float;
array za[1024] : float, zp[1024] : float;

k := 0;
while (k < 1024) {
  zp[k] := intToFloat(k) * 0.01 + 0.5;
  za[k] := intToFloat(k) * 0.002;
  k := k + 1
};

rep := 0;
while (rep < 100000) {
  j := 1;
  while (j < 31) {
    k := 1;
    while (k < 31) {
      idx := j * 32 + k;
      qa := zp[(j - 1) * 32 + k + 1] + zp[(j + 1) * 32 + k + 1]
          - zp[(j - 1) * 32 + k - 1] - zp[(j + 1) * 32 + k - 1];
      za[idx] := za[idx] + 0.175 * (qa - za[idx]);
      k := k + 1
    };
    j := j + 1
  };
  rep := rep + 1
}
