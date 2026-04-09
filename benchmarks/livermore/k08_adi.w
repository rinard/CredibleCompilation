var i : int, j : int, rep : int, r : float, idx : int;
array u[1024] : float, z[1024] : float;

i := 0;
while (i < 1024) {
  u[i] := intToFloat(i) * 0.01;
  z[i] := intToFloat(i) * 0.005 + 0.5;
  i := i + 1
};

r := 0.25;

rep := 0;
while (rep < 10000) {
  j := 1;
  while (j < 31) {
    i := 1;
    while (i < 31) {
      idx := j * 32 + i;
      u[idx] := u[idx] + r * (z[idx + 1] + z[idx - 1] + z[idx + 32] + z[idx - 32] - 4.0 * z[idx]);
      i := i + 1
    };
    j := j + 1
  };
  rep := rep + 1
}
