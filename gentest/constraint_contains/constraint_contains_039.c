
int main() {
  int *x[5][5];
  int i1 = 2;
  int i2 = 1;
  struct { int *g1; } y[5];
  int j1 = 2;
  x[i1][i2] = y[j1].g1;
  return(0);
}
