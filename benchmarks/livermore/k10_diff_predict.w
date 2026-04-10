var i : int, j : int, rep : int, base : int, ar : float, br : float, cr : float;
array px[2525] : float, cx[2525] : float;

i := 0;
while (i < 101) {
  j := 0;
  while (j < 25) {
    px[i * 25 + j] := (intToFloat(i) + 1.0) * 0.01 + intToFloat(j) * 0.001;
    cx[i * 25 + j] := (intToFloat(i) + 1.0) * 0.02 + intToFloat(j) * 0.002;
    j := j + 1
  };
  i := i + 1
};

rep := 0;
while (rep < 10000) {
  i := 0;
  while (i < 101) {
    base := i * 25;
    ar := cx[base + 4];
    br := ar - px[base + 4];
    px[base + 4] := ar;
    cr := br - px[base + 5];
    px[base + 5] := br;
    ar := cr - px[base + 6];
    px[base + 6] := cr;
    br := ar - px[base + 7];
    px[base + 7] := ar;
    cr := br - px[base + 8];
    px[base + 8] := br;
    ar := cr - px[base + 9];
    px[base + 9] := cr;
    br := ar - px[base + 10];
    px[base + 10] := ar;
    cr := br - px[base + 11];
    px[base + 11] := br;
    px[base + 13] := cr - px[base + 12];
    px[base + 12] := cr;
    i := i + 1
  };
  rep := rep + 1
}
