var k : int, rep : int, s : float, stb5 : float,
    fuzz : float, buzz : float, fizz : float;
array sa[1001] : float, b[1001] : float;

stb5 := 0.1;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 0;
while (k < 1001) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  sa[k] := (buzz - fizz) * 0.1;
  k := k + 1
};

rep := 0;
while (rep < 10000) {
  b[0] := sa[0];
  k := 1;
  while (k < 1001) {
    b[k] := sa[k] + stb5 * b[k - 1];
    k := k + 1
  };
  rep := rep + 1
};

s := b[1000]
