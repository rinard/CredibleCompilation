var i : int, rep : int;
array x[1001] : float, y[1001] : float, z[1001] : float;

i := 0;
while (i < 1001) {
  x[i] := intToFloat(i) * 0.01;
  y[i] := intToFloat(i) * 0.02 + 1.0;
  z[i] := intToFloat(i) * 0.003;
  i := i + 1
};

rep := 0;
while (rep < 10000) {
  i := 1;
  while (i < 1001) {
    x[i] := z[i] * (y[i] - x[i - 1]);
    i := i + 1
  };
  rep := rep + 1
}
