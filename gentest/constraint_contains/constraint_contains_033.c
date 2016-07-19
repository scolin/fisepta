
int main() {
  struct { int *f1[5]; } x;
  int i1 = 2;
  struct { int *g1[5]; } y;
  int j1 = 2;
  x.f1[i1] = y.g1[j1];
  return(0);
}
