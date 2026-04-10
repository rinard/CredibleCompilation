var rep : int, k : int, j : int, t : float, s : float,
    kj : int, kj1 : int, kjm1 : int, kjp1 : int,
    kp1jm1 : int, km1j : int, kp1j : int, kp1jm1b : int;
array za[707] : float, zb[707] : float, zp[707] : float, zq[707] : float,
      zr[707] : float, zm[707] : float, zu[707] : float, zv[707] : float,
      zz[707] : float;

k := 0;
while (k < 7) {
  j := 0;
  while (j < 101) {
    kj := k * 101 + j;
    zp[kj] := intToFloat(k + 1) * 0.01 + intToFloat(j) * 0.001;
    zq[kj] := intToFloat(k + 1) * 0.005 + intToFloat(j) * 0.0005;
    zr[kj] := intToFloat(k + 1) * 0.02 + intToFloat(j) * 0.002 + 0.5;
    zm[kj] := intToFloat(k + 1) * 0.03 + intToFloat(j) * 0.003 + 1.0;
    zz[kj] := intToFloat(k + 1) * 0.015 + intToFloat(j) * 0.0015;
    zu[kj] := 0.0;
    zv[kj] := 0.0;
    za[kj] := 0.0;
    zb[kj] := 0.0;
    j := j + 1
  };
  k := k + 1
};

rep := 0;
while (rep < 10000) {
  t := 0.0037;
  s := 0.0041;

  k := 1;
  while (k < 6) {
    j := 1;
    while (j < 101) {
      kj := k * 101 + j;
      kjm1 := k * 101 + (j - 1);
      kp1jm1 := (k + 1) * 101 + (j - 1);
      km1j := (k - 1) * 101 + j;
      za[kj] := (zp[kp1jm1] + zq[kp1jm1] - zp[kjm1] - zq[kjm1])
              * (zr[kj] + zr[kjm1])
              / (zm[kjm1] + zm[kp1jm1]);
      zb[kj] := (zp[kjm1] + zq[kjm1] - zp[kj] - zq[kj])
              * (zr[kj] + zr[km1j])
              / (zm[kj] + zm[kjm1]);
      j := j + 1
    };
    k := k + 1
  };

  k := 1;
  while (k < 6) {
    j := 1;
    while (j < 101) {
      kj := k * 101 + j;
      kjm1 := k * 101 + (j - 1);
      km1j := (k - 1) * 101 + j;
      if (j + 1 < 101) { kjp1 := k * 101 + (j + 1) } else { kjp1 := kj };
      if (k + 1 < 7) { kp1j := (k + 1) * 101 + j } else { kp1j := kj };
      zu[kj] := zu[kj] + s * (za[kj] * (zz[kj] - zz[kjp1])
                - za[kjm1] * (zz[kj] - zz[kjm1])
                - zb[kj] * (zz[kj] - zz[km1j])
                + zb[kp1j] * (zz[kj] - zz[kp1j]));
      zv[kj] := zv[kj] + s * (za[kj] * (zr[kj] - zr[kjp1])
                - za[kjm1] * (zr[kj] - zr[kjm1])
                - zb[kj] * (zr[kj] - zr[km1j])
                + zb[kp1j] * (zr[kj] - zr[kp1j]));
      j := j + 1
    };
    k := k + 1
  };

  k := 1;
  while (k < 6) {
    j := 1;
    while (j < 101) {
      kj := k * 101 + j;
      zr[kj] := zr[kj] + t * zu[kj];
      zz[kj] := zz[kj] + t * zv[kj];
      j := j + 1
    };
    k := k + 1
  };

  rep := rep + 1
}
