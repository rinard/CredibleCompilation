var rep : int, kx : int, ky : int, nl1 : int, nl2 : int,
    a11 : float, a12 : float, a13 : float,
    a21 : float, a22 : float, a23 : float,
    a31 : float, a32 : float, a33 : float,
    sig : float, nl : int, idx : int, idx_yp : int, idx_ym : int, idx_xp : int, idx_xm : int;
array u1[1010] : float, u2[1010] : float, u3[1010] : float,
      du1[101] : float, du2[101] : float, du3[101] : float;

nl := 0;
while (nl < 2) {
  ky := 0;
  while (ky < 101) {
    kx := 0;
    while (kx < 5) {
      idx := nl * 505 + ky * 5 + kx;
      u1[idx] := intToFloat(nl + 1) * 0.01 * intToFloat(ky) + 0.001 * intToFloat(kx);
      u2[idx] := intToFloat(nl + 1) * 0.02 * intToFloat(ky) + 0.002 * intToFloat(kx);
      u3[idx] := intToFloat(nl + 1) * 0.03 * intToFloat(ky) + 0.003 * intToFloat(kx);
      kx := kx + 1
    };
    ky := ky + 1
  };
  nl := nl + 1
};

ky := 0;
while (ky < 101) {
  du1[ky] := 0.0;
  du2[ky] := 0.0;
  du3[ky] := 0.0;
  ky := ky + 1
};

a11 := 0.1;  a12 := 0.2;  a13 := 0.3;
a21 := 0.05; a22 := 0.15; a23 := 0.25;
a31 := 0.02; a32 := 0.12; a33 := 0.22;
sig := 0.5;

rep := 0;
while (rep < 10000) {
  nl1 := 0;
  nl2 := 1;
  kx := 1;
  while (kx < 3) {
    ky := 1;
    while (ky < 101) {
      if (ky + 1 < 101) {
        idx_yp := nl1 * 505 + (ky + 1) * 5 + kx
      } else {
        idx_yp := nl1 * 505 + ky * 5 + kx
      };
      idx_ym := nl1 * 505 + (ky - 1) * 5 + kx;
      idx := nl1 * 505 + ky * 5 + kx;
      idx_xp := nl1 * 505 + ky * 5 + (kx + 1);
      idx_xm := nl1 * 505 + ky * 5 + (kx - 1);
      du1[ky] := u1[idx_yp] - u1[idx_ym];
      du2[ky] := u2[idx_yp] - u2[idx_ym];
      du3[ky] := u3[idx_yp] - u3[idx_ym];
      u1[nl2 * 505 + ky * 5 + kx] := u1[idx]
        + a11 * du1[ky] + a12 * du2[ky] + a13 * du3[ky]
        + sig * (u1[idx_xp] - 2.0 * u1[idx] + u1[idx_xm]);
      u2[nl2 * 505 + ky * 5 + kx] := u2[idx]
        + a21 * du1[ky] + a22 * du2[ky] + a23 * du3[ky]
        + sig * (u2[idx_xp] - 2.0 * u2[idx] + u2[idx_xm]);
      u3[nl2 * 505 + ky * 5 + kx] := u3[idx]
        + a31 * du1[ky] + a32 * du2[ky] + a33 * du3[ky]
        + sig * (u3[idx_xp] - 2.0 * u3[idx] + u3[idx_xm]);
      ky := ky + 1
    };
    kx := kx + 1
  };
  rep := rep + 1
}
