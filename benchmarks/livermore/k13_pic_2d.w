var ip : int, rep : int, i1 : int, j1 : int, i2 : int, j2 : int,
    fuzz : float, buzz : float, fizz : float, ds : float, dw : float,
    col : int, row : int;
array p_x[64] : float, p_y[64] : float, p_vx[64] : float, p_vy[64] : float, b[4096] : float, c[4096] : float, h[4096] : float, y[1001] : float, z[1001] : float, e[96] : int, f[96] : int;
fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
ip := 0;
while (ip < 4096) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  b[ip] := (buzz - fizz) * 0.1;
  ip := ip + 1
};
fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
ip := 0;
while (ip < 4096) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  c[ip] := (buzz - fizz) * 0.1;
  ip := ip + 1
};
fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
ip := 0;
while (ip < 1001) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  y[ip] := (buzz - fizz) * 0.1;
  ip := ip + 1
};
fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
ip := 0;
while (ip < 1001) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  z[ip] := (buzz - fizz) * 0.1;
  ip := ip + 1
};
ip := 0;
while (ip < 96) {
  e[ip] := ip % 64;
  f[ip] := ip % 64;
  ip := ip + 1
};
rep := 0;
while (rep < 10000) {
  ds := 1.0;
  dw := 0.5;
  col := 0;
  while (col < 4) {
    row := 0;
    while (row < 64) {
      if (col == 0) { p_x[row] := ds }
      else { if (col == 1) { p_y[row] := ds }
      else { if (col == 2) { p_vx[row] := ds }
      else { p_vy[row] := ds } } };
      ds := ds + dw;
      row := row + 1
    };
    col := col + 1
  };
  ip := 0;
  while (ip < 4096) {
    h[ip] := 0.0;
    ip := ip + 1
  };
  ip := 0;
  while (ip < 64) {
    i1 := floatToInt(p_x[ip]) % 64;
    if (i1 < 0) { i1 := i1 + 64 } else { skip };
    j1 := floatToInt(p_y[ip]) % 64;
    if (j1 < 0) { j1 := j1 + 64 } else { skip };
    p_vx[ip] := p_vx[ip] + b[j1 * 64 + i1];
    p_vy[ip] := p_vy[ip] + c[j1 * 64 + i1];
    p_x[ip] := p_x[ip] + p_vx[ip];
    p_y[ip] := p_y[ip] + p_vy[ip];
    i2 := (floatToInt(p_x[ip]) % 64) - 1;
    if (i2 < 0) { i2 := i2 + 64 } else { skip };
    j2 := (floatToInt(p_y[ip]) % 64) - 1;
    if (j2 < 0) { j2 := j2 + 64 } else { skip };
    p_x[ip] := p_x[ip] + y[i2 + 32];
    p_y[ip] := p_y[ip] + z[j2 + 32];
    if (i2 + 32 >= 0) { if (i2 + 32 < 96) { i2 := i2 + e[i2 + 32] } else { skip } } else { skip };
    if (j2 + 32 >= 0) { if (j2 + 32 < 96) { j2 := j2 + f[j2 + 32] } else { skip } } else { skip };
    if (j2 >= 0) { if (j2 < 64) { if (i2 >= 0) { if (i2 < 64) {
      h[j2 * 64 + i2] := h[j2 * 64 + i2] + 1.0
    } else { skip } } else { skip } } else { skip } } else { skip };
    ip := ip + 1
  };
  rep := rep + 1
}
