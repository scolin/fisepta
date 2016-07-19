
int main() {
  int *x[5];
  int i1 = 2;
  struct { int *g1[5]; } y;
  int j1 = 2;
  x[i1] = y.g1[j1];
  return(0);
}
