var rep : int, i : int, m : int, i1 : int, k : int, k2 : int, k3 : int,
    j2 : int, j4 : int, j5 : int, ii : int, lb : int, n : int,
    zval : int,
    r : float, s : float, t : float, tmp : float,
    fuzz : float, buzz : float, fizz : float;
array d[300] : float, plan[300] : float, zone[300] : int;
n := 75;
ii := n / 3;
lb := ii + ii;
r := 0.1;
s := 0.1;
t := 0.1;
fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
i := 0;
while (i < 300) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  d[i] := (buzz - fizz) * 0.1;
  i := i + 1
};
fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
i := 0;
while (i < 300) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  plan[i] := (buzz - fizz) * 0.1;
  i := i + 1
};
i := 0;
while (i < 300) {
  zone[i] := i % (n + 1);
  i := i + 1
};
zone[0] := 5;
rep := 0;
while (rep < 10000) {
  ii := n / 3;
  lb := ii + ii;
  k2 := 0;
  k3 := 0;
  i1 := 1;
  m := 1;
  LABEL410:;
  j2 := (n + n) * (m - 1) + 1;
  k := 1;
  while (k <= n) {
    k2 := k2 + 1;
    j4 := j2 + k + k;
    if (j4 - 1 < 0) { goto KBREAK } else { skip };
    if (j4 - 1 >= 300) { goto KBREAK } else { skip };
    j5 := zone[j4 - 1];
    if (j5 < n) {
      if (j5 < 1) {
        goto KBREAK
      } else {
        if (j5 + lb < n) {
          tmp := plan[j5 - 1] - t
        } else {
          if (j5 + ii < n) {
            tmp := plan[j5 - 1] - s
          } else {
            tmp := plan[j5 - 1] - r
          }
        }
      }
    } else {
      if (j5 == n) {
        goto KBREAK
      } else {
        if (j5 - 1 < 0) { goto KBREAK } else { skip };
        if (j5 - 1 >= 300) { goto KBREAK } else { skip };
        if (j5 - 5 < 0) { goto KBREAK } else { skip };
        k3 := k3 + 1;
        tmp := d[j5 - 1] - (d[j5 - 2] * (t - d[j5 - 3]) * (t - d[j5 - 3])
               + (s - d[j5 - 4]) * (s - d[j5 - 4])
               + (r - d[j5 - 5]) * (r - d[j5 - 5]))
      }
    };
    if (tmp < 0.0) {
      if (j4 - 2 < 0) { goto KBREAK } else { skip };
      if (j4 - 2 >= 300) { goto KBREAK } else { skip };
      zval := zone[j4 - 2];
      if (zval < 0) {
        goto KCONT
      } else {
        if (zval == 0) {
          goto KBREAK
        } else {
          skip
        }
      }
    } else {
      if (tmp > 0.0) {
        if (j4 - 2 < 0) { goto KBREAK } else { skip };
        if (j4 - 2 >= 300) { goto KBREAK } else { skip };
        zval := zone[j4 - 2];
        if (zval > 0) {
          goto KCONT
        } else {
          if (zval == 0) {
            goto KBREAK
          } else {
            skip
          }
        }
      } else {
        goto KBREAK
      }
    };
    m := m + 1;
    if (m > zone[0]) { m := 1 } else { skip };
    if (i1 != m) {
      goto LABEL410
    } else {
      goto KBREAK
    };
    KCONT:;
    k := k + 1
  };
  KBREAK:;
  rep := rep + 1
}
