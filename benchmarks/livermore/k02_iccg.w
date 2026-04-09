var k : int, rep : int;
array x[1024] : float, v[1024] : float, w[1024] : float;

k := 0;
while (k < 1024) {
  x[k] := intToFloat(k) * 0.01;
  v[k] := intToFloat(k) * 0.001 + 0.1;
  w[k] := intToFloat(k) * 0.002 + 0.05;
  k := k + 1
};

rep := 0;
while (rep < 10000) {
  k := 2;
  while (k < 1024) {
    x[k] := x[k] - v[k] * x[k - 1] - w[k] * x[k - 2];
    k := k + 1
  };
  rep := rep + 1
}
