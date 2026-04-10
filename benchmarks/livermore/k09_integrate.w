var i : int, j : int, rep : int, base : int,
    dm28 : float, dm27 : float, dm26 : float, dm25 : float,
    dm24 : float, dm23 : float, dm22 : float, c0 : float;
array px[2525] : float;

i := 0;
while (i < 101) {
  j := 0;
  while (j < 25) {
    px[i * 25 + j] := (intToFloat(i) + 1.0) * 0.01 + intToFloat(j) * 0.001;
    j := j + 1
  };
  i := i + 1
};

dm28 := 0.01; dm27 := 0.02; dm26 := 0.03; dm25 := 0.04;
dm24 := 0.05; dm23 := 0.06; dm22 := 0.07; c0 := 0.5;

rep := 0;
while (rep < 10000) {
  i := 0;
  while (i < 101) {
    base := i * 25;
    px[base] := dm28 * px[base + 12] + dm27 * px[base + 11] + dm26 * px[base + 10]
              + dm25 * px[base + 9]  + dm24 * px[base + 8]  + dm23 * px[base + 7]
              + dm22 * px[base + 6]  + c0 * (px[base + 4] + px[base + 5]) + px[base + 2];
    i := i + 1
  };
  rep := rep + 1
}
