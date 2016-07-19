
int main() {
  struct { int *f1[5]; } x;
  int i1 = 2;
  struct { int *g1; } y[5];
  int j1 = 2;
  x.f1[i1] = y[j1].g1;
  return(0);
}
