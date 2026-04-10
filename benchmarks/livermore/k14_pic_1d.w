var k : int, rep : int, flx : float;
array grd[1001] : float, dex[1001] : float, xi[1001] : float, ex[1001] : float, ex1[1001] : float, dex1[1001] : float, vx[1001] : float, xx[1001] : float, rx[1001] : float, rh[2048] : float, ix[1001] : int, ir[1001] : int;

k := 0;
while (k < 1001) {
  grd[k] := intToFloat(k % 512) + 1.5;
  ex[k] := intToFloat(k) * 0.001;
  dex[k] := intToFloat(k) * 0.0005;
  k := k + 1
};

k := 0;
while (k < 2048) {
  rh[k] := 0.0;
  k := k + 1
};

flx := 0.001;

rep := 0;
while (rep < 10000) {
  k := 0;
  while (k < 512) {
    vx[k] := 0.0;
    xx[k] := 0.0;
    ix[k] := floatToInt(grd[k]);
    xi[k] := intToFloat(ix[k]);
    ex1[k] := ex[ix[k] - 1];
    dex1[k] := dex[ix[k] - 1];
    k := k + 1
  };
  k := 0;
  while (k < 512) {
    vx[k] := vx[k] + ex1[k] + (xx[k] - xi[k]) * dex1[k];
    xx[k] := xx[k] + vx[k] + flx;
    ir[k] := floatToInt(xx[k]);
    rx[k] := xx[k] - intToFloat(ir[k]);
    ir[k] := ir[k] % 2048;
    if (ir[k] < 0) { ir[k] := ir[k] + 2048 } else { skip };
    ir[k] := ir[k] + 1;
    xx[k] := rx[k] + intToFloat(ir[k]);
    k := k + 1
  };
  k := 0;
  while (k < 512) {
    rh[ir[k] - 1] := rh[ir[k] - 1] + 1.0 - rx[k];
    rh[ir[k]] := rh[ir[k]] + rx[k];
    k := k + 1
  };
  rep := rep + 1
}
