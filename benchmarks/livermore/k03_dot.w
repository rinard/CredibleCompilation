var i : int, rep : int, q : float;
array x[1024] : float, z[1024] : float;

i := 0;
while (i < 1024) {
  x[i] := intToFloat(i) * 0.001;
  z[i] := intToFloat(i) * 0.002;
  i := i + 1
};

rep := 0;
while (rep < 10000) {
  q := 0.0;
  i := 0;
  while (i < 1024) {
    q := q + x[i] * z[i];
    i := i + 1
  };
  rep := rep + 1
}
