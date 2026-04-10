var k : int, rep : int, expx : float, s : float;
array x[1001] : float, y[1001] : float;

k := 0;
while (k < 1001) {
  x[k] := intToFloat(k) * 0.01 + 0.01;
  k := k + 1
};

s := 0.0;

rep := 0;
while (rep < 10000) {
  k := 0;
  while (k < 1001) {
    expx := exp(x[k]);
    y[k] := x[k] / (expx - 1.0);
    k := k + 1
  };
  rep := rep + 1
};

s := y[0]
