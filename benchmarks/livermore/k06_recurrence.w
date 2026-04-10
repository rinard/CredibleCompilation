var i : int, k : int, rep : int,
    fuzz : float, buzz : float, fizz : float;
array w[1001] : float, b[4096] : float;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
i := 0;
while (i < 4096) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  b[i] := (buzz - fizz) * 0.1;
  i := i + 1
};

rep := 0;
while (rep < 1000) {
  i := 0;
  while (i < 1001) {
    w[i] := 0.0;
    i := i + 1
  };
  w[0] := 0.01;
  i := 1;
  while (i < 64) {
    k := 0;
    while (k < i) {
      w[i] := w[i] + b[k * 64 + i] * w[i - k - 1];
      k := k + 1
    };
    i := i + 1
  };
  rep := rep + 1
}
