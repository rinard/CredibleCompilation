var i : int, rep : int;
array x[1024] : int;

i := 0;
while (i < 1024) {
  x[i] := i;
  i := i + 1
};

rep := 0;
while (rep < 10000) {
  i := 1;
  while (i < 1024) {
    x[i] := x[i] + x[i - 1];
    i := i + 1
  };
  rep := rep + 1
}
