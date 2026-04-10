var k : int, i : int, rep : int, stb5 : float, kb5i : int,
    fuzz : float, buzz : float, fizz : float;
array b5[101] : float, sa[101] : float, sb[101] : float;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 0;
while (k < 101) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  sa[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 0;
while (k < 101) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  sb[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

rep := 0;
while (rep < 10000) {
  stb5 := 0.5;
  kb5i := 0;
  k := 0;
  while (k < 101) {
    b5[k + kb5i] := sa[k] + stb5 * sb[k];
    stb5 := b5[k + kb5i] - stb5;
    k := k + 1
  };
  i := 1;
  while (i < 102) {
    k := 101 - i;
    b5[k + kb5i] := sa[k] + stb5 * sb[k];
    stb5 := b5[k + kb5i] - stb5;
    i := i + 1
  };
  rep := rep + 1
};

stb5 := b5[100]
