var i : int, k : int, rep : int;
array w[64] : float, b[1024] : float;

i := 0;
while (i < 1024) {
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
      w[i] := w[i] + b[i * 64 + k] * w[i - k - 1];
      k := k + 1
    };
    i := i + 1
  };
  rep := rep + 1
}
