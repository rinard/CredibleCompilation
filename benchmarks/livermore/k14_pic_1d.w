var k : int, rep : int, ix : int, xi : float, flx : float;
array rx[1024] : float, vx[1024] : float, ex[1024] : float, dex[1024] : float;

k := 0;
while (k < 1024) {
  rx[k]  := intToFloat(k) * 0.5 + 0.5;
  vx[k]  := 0.0;
  ex[k]  := intToFloat(k) * 0.001;
  dex[k] := intToFloat(k) * 0.0005;
  k := k + 1
};

flx := 0.001;

rep := 0;
while (rep < 10000) {
  k := 0;
  while (k < 512) {
    ix := floatToInt(rx[k]);
    xi := intToFloat(ix);
    vx[k] := vx[k] + ex[ix] + (rx[k] - xi) * dex[ix];
    rx[k] := rx[k] + vx[k] + flx;
    k := k + 1
  };
  rep := rep + 1
}
