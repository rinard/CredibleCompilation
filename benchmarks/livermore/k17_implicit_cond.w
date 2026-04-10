var rep : int, i : int, j : int, ink : int, n : int, k : int,
    scale : float, xnm : float, e6 : float, e3 : float,
    xnei : float, xnc : float,
    fuzz : float, buzz : float, fizz : float;
array vsp[101] : float, vstp[101] : float, vxne[101] : float,
      vxnd[101] : float, ve3[101] : float, vlr[101] : float,
      vlin[101] : float;

n := 101;

rep := 0;
while (rep < 10000) {
  i := n - 2;
  j := 0;
  ink := 0 - 1;
  scale := 5.0 / 3.0;
  xnm := 1.0 / 3.0;
  e6 := 1.03 / 3.07;
  goto L61;
  L60:;
  e6 := xnm * vsp[i] + vstp[i];
  vxne[i] := e6;
  xnm := e6;
  ve3[i] := e6;
  i := i + ink;
  if (i == j) goto L62;
  L61:;
  e3 := xnm * vlr[i] + vlin[i];
  xnei := vxne[i];
  vxnd[i] := e6;
  xnc := scale * e3;
  if (xnm > xnc) goto L60;
  if (xnei > xnc) goto L60;
  ve3[i] := e3;
  e6 := e3 + e3 - xnm;
  vxne[i] := e3 + e3 - xnei;
  xnm := e6;
  i := i + ink;
  if (i != j) goto L61;
  L62:;
  rep := rep + 1
}
