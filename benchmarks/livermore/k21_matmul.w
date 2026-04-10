var i : int, j : int, k : int, rep : int;
array px[2525] : float, vy[2525] : float, cx[2525] : float;

i := 0;
while (i < 101) {
  j := 0;
  while (j < 25) {
    px[i * 25 + j] := intToFloat(i + j) * 0.01;
    cx[i * 25 + j] := intToFloat(i - j + 25) * 0.01;
    j := j + 1
  };
  i := i + 1
};

i := 0;
while (i < 25) {
  j := 0;
  while (j < 101) {
    vy[i * 101 + j] := intToFloat(i * j % 50) * 0.002;
    j := j + 1
  };
  i := i + 1
};

rep := 0;
while (rep < 1000) {
  k := 0;
  while (k < 25) {
    i := 0;
    while (i < 25) {
      j := 0;
      while (j < 101) {
        px[j * 25 + i] := px[j * 25 + i] + vy[k * 101 + i] * cx[j * 25 + k];
        j := j + 1
      };
      i := i + 1
    };
    k := k + 1
  };
  rep := rep + 1
}
