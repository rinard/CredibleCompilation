var rep : int, kx : int, ky : int, nl1 : int, nl2 : int,
    a11 : float, a12 : float, a13 : float,
    a21 : float, a22 : float, a23 : float,
    a31 : float, a32 : float, a33 : float,
    sig : float, nl : int, idx : int, idx_yp : int, idx_ym : int, idx_xp : int, idx_xm : int,
    fuzz : float, buzz : float, fizz : float;
array u1[1010] : float, u2[1010] : float, u3[1010] : float,
      du1[101] : float, du2[101] : float, du3[101] : float,
      spacer[39] : float;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
idx := 0;
while (idx < 39) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  spacer[idx] := (buzz - fizz) * 0.1;
  idx := idx + 1
};
a11 := spacer[0];  a12 := spacer[1];  a13 := spacer[2];
a21 := spacer[3];  a22 := spacer[4];  a23 := spacer[5];
a31 := spacer[6];  a32 := spacer[7];  a33 := spacer[8];
sig := spacer[33];

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
idx := 0;
while (idx < 1010) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  u1[idx] := (buzz - fizz) * 0.1;
  idx := idx + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
idx := 0;
while (idx < 1010) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  u2[idx] := (buzz - fizz) * 0.1;
  idx := idx + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
idx := 0;
while (idx < 1010) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  u3[idx] := (buzz - fizz) * 0.1;
  idx := idx + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
ky := 0;
while (ky < 101) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  du1[ky] := (buzz - fizz) * 0.1;
  ky := ky + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
ky := 0;
while (ky < 101) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  du2[ky] := (buzz - fizz) * 0.1;
  ky := ky + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
ky := 0;
while (ky < 101) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  du3[ky] := (buzz - fizz) * 0.1;
  ky := ky + 1
};

rep := 0;
while (rep < 10000) {
  nl1 := 0;
  nl2 := 1;
  kx := 1;
  while (kx < 3) {
    ky := 1;
    while (ky < 99) {
      idx_yp := nl1 * 505 + (ky + 1) * 5 + kx;
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
