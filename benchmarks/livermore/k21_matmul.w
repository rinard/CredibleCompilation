var i : int, j : int, k : int, rep : int,
    fuzz : float, buzz : float, fizz : float;
array px[2525] : float, vy[2525] : float, cx[2525] : float;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
i := 0;
while (i < 2525) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  px[i] := (buzz - fizz) * 0.1;
  i := i + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
i := 0;
while (i < 2525) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  cx[i] := (buzz - fizz) * 0.1;
  i := i + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
i := 0;
while (i < 2525) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  vy[i] := (buzz - fizz) * 0.1;
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
