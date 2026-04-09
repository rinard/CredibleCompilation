var k : int, m : int, rep : int, xm : float, xk : float;
array x[1024] : float;

k := 0;
while (k < 1024) {
  x[k] := intToFloat(1024 - k) * 0.01;
  k := k + 1
};

rep := 0;
while (rep < 10000) {
  m := 0;
  xm := x[0];
  k := 1;
  while (k < 1024) {
    xk := x[k];
    if (xk < xm) {
      m := k;
      xm := xk
    } else {
      skip
    };
    k := k + 1
  };
  rep := rep + 1
}
