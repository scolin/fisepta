
int main() {
  int *x[5][5];
  int i1 = 2;
  int i2 = 1;
  struct { int *g1[5]; } y;
  int j1 = 2;
  x[i1][i2] = y.g1[j1];
  return(0);
}
