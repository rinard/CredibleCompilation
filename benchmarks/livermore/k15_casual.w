var i : int, rep : int, seed : int, idx : int, ng : int;
array vx[1024] : float, ix1[1024] : int;

seed := 12345;
i := 0;
while (i < 1024) {
  seed := seed * 6364136223846793005 + 1442695040888963407;
  vx[i] := intToFloat(seed % 1000) * 0.001;
  i := i + 1
};

rep := 0;
while (rep < 10000) {
  ng := 0;
  i := 0;
  while (i < 1024) {
    seed := seed * 6364136223846793005 + 1442695040888963407;
    idx := seed % 512;
    if (idx < 0) { idx := 0 - idx } else { skip };
    ix1[ng] := idx;
    ng := ng + 1;
    i := i + 1
  };
  i := 0;
  while (i < ng) {
    idx := ix1[i];
    vx[idx] := vx[idx] + 1.0;
    i := i + 1
  };
  rep := rep + 1
}
