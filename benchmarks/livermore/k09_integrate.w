var i : int, rep : int, c0 : float, c1 : float, c2 : float, c3 : float;
array px[1024] : float, cx1[1024] : float, cx2[1024] : float, cx3[1024] : float;

i := 0;
while (i < 1024) {
  px[i]  := intToFloat(i) * 0.01;
  cx1[i] := intToFloat(i) * 0.005;
  cx2[i] := intToFloat(i) * 0.003;
  cx3[i] := intToFloat(i) * 0.001;
  i := i + 1
};

c0 := 0.5;
c1 := 0.25;
c2 := 0.125;
c3 := 0.0625;

rep := 0;
while (rep < 10000) {
  i := 0;
  while (i < 1024) {
    px[i] := c0 * px[i] + c1 * cx1[i] + c2 * cx2[i] + c3 * cx3[i];
    i := i + 1
  };
  rep := rep + 1
}
