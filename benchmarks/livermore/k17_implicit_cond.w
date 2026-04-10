var k : int, rep : int, dt : float,
    fuzz : float, buzz : float, fizz : float;
array vy[1024] : float;

dt := 0.1;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
k := 0;
while (k < 1024) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  vy[k] := (buzz - fizz) * 0.1;
  k := k + 1
};
k := 0;
while (k < 1024) {
  if (k % 2 == 0) { vy[k] := 0.0 - vy[k] } else { skip };
  k := k + 1
};

rep := 0;
while (rep < 10000) {
  k := 1;
  while (k < 1024) {
    if (vy[k] < 0.0) {
      vy[k] := vy[k] - dt * vy[k - 1]
    } else {
      skip
    };
    k := k + 1
  };
  rep := rep + 1
}
