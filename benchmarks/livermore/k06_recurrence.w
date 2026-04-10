var i : int, k : int, rep : int;
array w[64] : float, b[4096] : float;

i := 0;
while (i < 4096) {
  b[i] := intToFloat(i) * 0.0001;
  i := i + 1
};

rep := 0;
while (rep < 1000) {
  i := 0;
  while (i < 64) {
    w[i] := 0.0;
    i := i + 1
  };
  i := 1;
  while (i < 64) {
    w[i] := 0.01;
    k := 0;
    while (k < i) {
      w[i] := w[i] + b[k * 64 + i] * w[i - k - 1];
      k := k + 1
    };
    i := i + 1
  };
  rep := rep + 1
}
