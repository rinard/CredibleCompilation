var ip : int, rep : int, i1 : int, j1 : int, i2 : int, j2 : int;
array p_x[512] : float, p_y[512] : float, p_vx[512] : float, p_vy[512] : float, b[4096] : float, c[4096] : float, h[4096] : float, y[1001] : float, z[1001] : float, e[96] : int, f[96] : int;

ip := 0;
while (ip < 512) {
  p_x[ip] := intToFloat(ip % 64) + 0.5;
  p_y[ip] := intToFloat(ip / 64) + 0.5;
  p_vx[ip] := 0.001;
  p_vy[ip] := 0.001;
  ip := ip + 1
};

ip := 0;
while (ip < 4096) {
  b[ip] := intToFloat(ip) * 0.0001;
  c[ip] := intToFloat(ip) * 0.00005;
  h[ip] := 0.0;
  ip := ip + 1
};

ip := 0;
while (ip < 1001) {
  y[ip] := 0.001;
  z[ip] := 0.001;
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
  ip := 0;
  while (ip < 512) {
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
    i2 := i2 + e[i2 + 32];
    j2 := j2 + f[j2 + 32];
    h[j2 * 64 + i2] := h[j2 * 64 + i2] + 1.0;
    ip := ip + 1
  };
  rep := rep + 1
}
