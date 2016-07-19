
int main() {
  struct { int *f1[5]; } x;
  int i1 = 2;
  struct { struct { int *g2; } g1; } y;
  x.f1[i1] = y.g1.g2;
  return(0);
}
