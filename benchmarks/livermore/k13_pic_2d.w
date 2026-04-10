var k : int, rep : int, ix : int, iy : int, idx : int, dt : float, ex_val : float;
array px[512] : float, py[512] : float, vx[512] : float, vy[512] : float, E[1024] : float;

k := 0;
while (k < 512) {
  px[k] := intToFloat(k % 32) + 0.5;
  py[k] := intToFloat(k / 32) + 0.5;
  vx[k] := 0.001;
  vy[k] := 0.001;
  k := k + 1
};

k := 0;
while (k < 1024) {
  E[k] := intToFloat(k) * 0.0001;
  k := k + 1
};

dt := 0.01;

rep := 0;
while (rep < 10000) {
  k := 0;
  while (k < 512) {
    ix := floatToInt(px[k]);
    iy := floatToInt(py[k]);
    idx := ix * 32 + iy;
    ex_val := E[idx];
    vx[k] := vx[k] + ex_val * dt;
    vy[k] := vy[k] + ex_val * dt;
    px[k] := px[k] + vx[k] * dt;
    py[k] := py[k] + vy[k] * dt;
    k := k + 1
  };
  rep := rep + 1
}
