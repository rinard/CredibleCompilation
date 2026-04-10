var rep : int, j : int, k : int, ar : float, br : float,
    r : float, s : float, t : float, jk : int, jk1 : int,
    jp1k : int, jm1k : int, jkm1 : int, jkp1 : int,
    jp1km1 : int, jm1kp1 : int,
    fuzz : float, buzz : float, fizz : float;
array vy[2525] : float, vh[707] : float, vf[707] : float,
      vg[707] : float, vs[707] : float;

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
j := 0;
while (j < 707) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  vh[j] := (buzz - fizz) * 0.1;
  j := j + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
j := 0;
while (j < 707) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  vf[j] := (buzz - fizz) * 0.1;
  j := j + 1
};
j := 0;
while (j < 707) {
  if (vf[j] < 0.001) { vf[j] := 0.001 } else { skip };
  j := j + 1
};

fuzz := 0.001234500;
buzz := 1.0 + fuzz;
fizz := 1.1 * fuzz;
j := 0;
while (j < 707) {
  buzz := (1.0 - fuzz) * buzz + fuzz;
  fuzz := 0.0 - fuzz;
  vg[j] := (buzz - fizz) * 0.1;
  j := j + 1
};

j := 0;
while (j < 707) {
  vs[j] := 0.0;
  j := j + 1
};

j := 0;
while (j < 2525) {
  vy[j] := 0.0;
  j := j + 1
};

rep := 0;
while (rep < 10000) {
  ar := 0.053;
  br := 0.073;
  j := 1;
  while (j < 7) {
    k := 1;
    while (k < 101) {
      jk := j * 101 + k;
      jp1k := (j + 1) * 101 + k;
      jkm1 := j * 101 + (k - 1);
      jp1km1 := (j + 1) * 101 + (k - 1);
      if (j + 1 >= 7) {
        vy[jk] := 0.0
      } else {
        if (vh[jp1k] > vh[jk]) { t := ar } else { t := br };
        if (vf[jk] < vf[jkm1]) {
          if (vh[jkm1] > vh[jp1km1]) { r := vh[jkm1] } else { r := vh[jp1km1] };
          s := vf[jkm1]
        } else {
          if (vh[jk] > vh[jp1k]) { r := vh[jk] } else { r := vh[jp1k] };
          s := vf[jk]
        };
        vy[jk] := (vg[jk] * vg[jk] + r * r) * t / s;
        jkp1 := j * 101 + (k + 1);
        jm1k := (j - 1) * 101 + k;
        jm1kp1 := (j - 1) * 101 + (k + 1);
        if (k + 1 >= 101) {
          vs[jk] := 0.0
        } else {
          if (vf[jk] < vf[jm1k]) {
            if (vg[jm1k] > vg[jm1kp1]) { r := vg[jm1k] } else { r := vg[jm1kp1] };
            s := vf[jm1k];
            t := br
          } else {
            if (vg[jk] > vg[jkp1]) { r := vg[jk] } else { r := vg[jkp1] };
            s := vf[jk];
            t := ar
          };
          vs[jk] := (vh[jk] * vh[jk] + r * r) * t / s
        }
      };
      k := k + 1
    };
    j := j + 1
  };
  rep := rep + 1
}
