var i : int, j : int, k : int, rep : int, s : float;
array a[1024] : float, b[1024] : float, c[1024] : float;

i := 0;
while (i < 32) {
  j := 0;
  while (j < 32) {
    a[i * 32 + j] := intToFloat(i + j) * 0.01;
    b[i * 32 + j] := intToFloat(i - j + 32) * 0.01;
    j := j + 1
  };
  i := i + 1
};

rep := 0;
while (rep < 1000) {
  i := 0;
  while (i < 32) {
    j := 0;
    while (j < 32) {
      s := 0.0;
      k := 0;
      while (k < 32) {
        s := s + a[i * 32 + k] * b[k * 32 + j];
        k := k + 1
      };
      c[i * 32 + j] := s;
      j := j + 1
    };
    i := i + 1
  };
  rep := rep + 1
}
