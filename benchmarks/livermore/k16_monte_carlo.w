var rep : int, i : int, m : int, i1 : int, k : int, k2 : int, k3 : int,
    j2 : int, j4 : int, j5 : int, ii : int, lb : int, n : int,
    seed : int, brk : int, done : int, zval : int,
    j4m1 : int, j4m2 : int, j5m1 : int, j5m2 : int, j5m3 : int,
    j5m4 : int, j5m5 : int, cont : int,
    r : float, s : float, t : float, tmp : float;
array d[300] : float, plan[300] : float, zone[300] : int;

n := 100;
ii := n / 3;
lb := ii + ii;
r := 0.1;
s := 0.2;
t := 0.3;
seed := 54321;

i := 0;
while (i < 300) {
  seed := seed * 6364136223846793005 + 1442695040888963407;
  d[i] := intToFloat(seed % 1000) * 0.001;
  if (d[i] < 0.0) { d[i] := 0.0 - d[i] } else { skip };
  seed := seed * 6364136223846793005 + 1442695040888963407;
  plan[i] := intToFloat(seed % 500) * 0.001;
  if (plan[i] < 0.0) { plan[i] := 0.0 - plan[i] } else { skip };
  seed := seed * 6364136223846793005 + 1442695040888963407;
  zone[i] := seed % 200;
  if (zone[i] < 0) { zone[i] := 0 - zone[i] } else { skip };
  i := i + 1
};
zone[0] := 5;

rep := 0;
while (rep < 10000) {
  i1 := 1;
  m := 1;
  k2 := 0;
  k3 := 0;
  done := 0;
  while (done == 0) {
    j2 := (n + n) * (m - 1) + 1;
    brk := 0;
    k := 1;
    while (k <= n) {
      if (brk == 0) {
        k2 := k2 + 1;
        j4 := j2 + k + k;
        j4m1 := (j4 - 1) % 300;
        if (j4m1 < 0) { j4m1 := j4m1 + 300 } else { skip };
        j4m2 := (j4 - 2) % 300;
        if (j4m2 < 0) { j4m2 := j4m2 + 300 } else { skip };
        j5 := zone[j4m1];
        if (j5 < 0) { j5 := 0 - j5 } else { skip };
        if (j5 >= 300) { j5 := j5 % 300 } else { skip };
        cont := 0;
        if (j5 < n) {
          if (j5 + lb < n) {
            tmp := plan[j5] - t
          } else {
            if (j5 + ii < n) {
              tmp := plan[j5] - s
            } else {
              tmp := plan[j5] - r
            }
          }
        } else {
          if (j5 == n) {
            brk := 1;
            cont := 1
          } else {
            k3 := k3 + 1;
            j5m1 := (j5 - 1) % 300;
            if (j5m1 < 0) { j5m1 := j5m1 + 300 } else { skip };
            j5m2 := (j5 - 2) % 300;
            if (j5m2 < 0) { j5m2 := j5m2 + 300 } else { skip };
            j5m3 := (j5 - 3) % 300;
            if (j5m3 < 0) { j5m3 := j5m3 + 300 } else { skip };
            j5m4 := (j5 - 4) % 300;
            if (j5m4 < 0) { j5m4 := j5m4 + 300 } else { skip };
            j5m5 := (j5 - 5) % 300;
            if (j5m5 < 0) { j5m5 := j5m5 + 300 } else { skip };
            tmp := d[j5m1] - (d[j5m2] * (t - d[j5m3]) * (t - d[j5m3])
                   + (s - d[j5m4]) * (s - d[j5m4])
                   + (r - d[j5m5]) * (r - d[j5m5]))
          }
        };
        if (cont == 0) {
          zval := zone[j4m2];
          if (tmp < 0.0) {
            if (zval < 0) {
              cont := 1
            } else {
              if (zval == 0) {
                brk := 1
              } else {
                skip
              }
            }
          } else {
            if (tmp > 0.0) {
              if (zval > 0) {
                cont := 1
              } else {
                if (zval == 0) {
                  brk := 1
                } else {
                  skip
                }
              }
            } else {
              brk := 1
            }
          };
          if (cont == 0) {
            if (brk == 0) {
              m := m + 1;
              if (m > zone[0]) { m := 1 } else { skip };
              if (i1 != m) {
                brk := 1
              } else {
                brk := 1
              }
            } else {
              skip
            }
          } else {
            skip
          }
        } else {
          skip
        }
      } else {
        skip
      };
      k := k + 1
    };
    if (brk == 0) {
      done := 1
    } else {
      if (i1 == m) {
        done := 1
      } else {
        skip
      }
    }
  };
  rep := rep + 1
}
