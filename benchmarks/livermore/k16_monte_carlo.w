var i : int, rep : int, seed : int, zone : int, plan : int, hits : int;
array d[1024] : float, weight[1024] : float, tally[64] : float;

seed := 67890;
i := 0;
while (i < 1024) {
  seed := seed * 6364136223846793005 + 1442695040888963407;
  d[i] := intToFloat(seed % 500 + 250) * 0.001;
  seed := seed * 6364136223846793005 + 1442695040888963407;
  weight[i] := intToFloat(seed % 100 + 1) * 0.01;
  i := i + 1
};

rep := 0;
while (rep < 10000) {
  i := 0;
  while (i < 64) {
    tally[i] := 0.0;
    i := i + 1
  };
  hits := 0;
  i := 0;
  while (i < 1024) {
    seed := seed * 6364136223846793005 + 1442695040888963407;
    zone := seed % 64;
    if (zone < 0) { zone := 0 - zone } else { skip };
    seed := seed * 6364136223846793005 + 1442695040888963407;
    plan := seed % 3;
    if (plan < 0) { plan := 0 - plan } else { skip };
    if (plan == 0) {
      tally[zone] := tally[zone] + weight[i] * d[i];
      hits := hits + 1
    } else {
      if (plan == 1) {
        tally[zone] := tally[zone] - weight[i] * d[i];
        hits := hits + 1
      } else {
        skip
      }
    };
    i := i + 1
  };
  rep := rep + 1
}
