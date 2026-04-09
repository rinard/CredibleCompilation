var i : int, rep : int;
array x[1024] : float, y[1024] : float;

i := 0;
while (i < 1024) {
  y[i] := intToFloat(i) * 0.01;
  i := i + 1
};

rep := 0;
while (rep < 10000) {
  i := 0;
  while (i < 1023) {
    x[i] := y[i + 1] - y[i];
    i := i + 1
  };
  rep := rep + 1
}
