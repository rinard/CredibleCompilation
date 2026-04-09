var k : int, rep : int, dt : float;
array vy[1024] : float;

k := 0;
while (k < 1024) {
  vy[k] := intToFloat(k - 512) * 0.01;
  k := k + 1
};

dt := 0.01;

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
