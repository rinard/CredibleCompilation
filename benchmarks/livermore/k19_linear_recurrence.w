var k : int, rep : int, s : float, stb5 : float;
array sa[1001] : float, b[1001] : float;

k := 0;
while (k < 1001) {
  sa[k] := intToFloat(k) * 0.001 + 0.5;
  k := k + 1
};

stb5 := 0.5;

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
