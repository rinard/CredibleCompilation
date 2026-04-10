var k : int, i : int, rep : int, ii : int, ipnt : int, ipntp : int;
array x[1001] : float, v[1001] : float;

k := 0;
while (k < 1001) {
  x[k] := intToFloat(k) * 0.01;
  v[k] := intToFloat(k) * 0.001 + 0.1;
  k := k + 1
};

rep := 0;
while (rep < 10000) {
  ii := 101;
  ipntp := 0;
  while (ii > 1) {
    ipnt := ipntp;
    ipntp := ipntp + ii;
    ii := ii / 2;
    i := ipntp;
    k := ipnt + 1;
    while (k < ipntp) {
      i := i + 1;
      x[i] := x[k] - v[k] * x[k - 1] - v[k + 1] * x[k + 1];
      k := k + 2
    }
  };
  rep := rep + 1
}
