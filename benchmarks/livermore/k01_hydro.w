var q : float, r : float, t : float, k : int, rep : int;
array x[1024] : float, y[1024] : float, z[1024] : float;

k := 0;
while (k < 1024) {
  y[k] := intToFloat(k) * 0.01;
  z[k] := intToFloat(k) * 0.02 + 1.0;
  k := k + 1
};

q := 1.5;
r := 2.0;
t := 3.0;

rep := 0;
while (rep < 10000) {
  k := 0;
  while (k < 1000) {
    x[k] := q + y[k] * (r * z[k + 10] + t * z[k + 11]);
    k := k + 1
  };
  rep := rep + 1
}
