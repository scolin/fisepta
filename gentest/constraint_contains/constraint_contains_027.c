
int main() {
  struct { int *f1; } x[5];
  int i1 = 2;
  int *y[5][5];
  int j1 = 2;
  int j2 = 1;
  x[i1].f1 = y[j1][j2];
  return(0);
}
