
int main() {
  struct { int *f1[5]; } x;
  int i1 = 2;
  int *y[5][5];
  int j1 = 2;
  int j2 = 1;
  x.f1[i1] = y[j1][j2];
  return(0);
}
