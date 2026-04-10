var i : int, j : int, rep : int, base : int,
    dm28 : float, dm27 : float, dm26 : float, dm25 : float,
    dm24 : float, dm23 : float, dm22 : float, c0 : float,
    fuzz : float, buzz : float, fizz : float;
array px[2525] : float, spacer[39] : float;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
i := 0;
while (i < 39) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  spacer[i] := (buzz - fizz) * 0.1;
  i := i + 1
};
dm22 := spacer[15]; dm23 := spacer[16]; dm24 := spacer[17]; dm25 := spacer[18];
dm26 := spacer[19]; dm27 := spacer[20]; dm28 := spacer[21]; c0 := spacer[11];

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
i := 0;
while (i < 2525) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  px[i] := (buzz - fizz) * 0.1;
  i := i + 1
};

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
