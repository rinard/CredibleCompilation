var i : int, rep : int, t : float, ar : float, cr : float;
array cx0[1024] : float, cx1[1024] : float, cx2[1024] : float, cx3[1024] : float, cx4[1024] : float;

i := 0;
while (i < 1024) {
  cx0[i] := intToFloat(i) * 0.01;
  cx1[i] := intToFloat(i) * 0.005;
  cx2[i] := intToFloat(i) * 0.003;
  cx3[i] := intToFloat(i) * 0.002;
  cx4[i] := intToFloat(i) * 0.001;
  i := i + 1
};

t := 0.037;

rep := 0;
while (rep < 10000) {
  i := 0;
  while (i < 1024) {
    ar := cx4[i];
    cr := t * ar + cx3[i];
    ar := t * cr + cx2[i];
    cr := t * ar + cx1[i];
    ar := t * cr + cx0[i];
    cx0[i] := ar;
    cx1[i] := cr;
    i := i + 1
  };
  rep := rep + 1
}
