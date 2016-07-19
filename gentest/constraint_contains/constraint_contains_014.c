
int main() {
  int *x[5];
  int i1 = 2;
  struct { struct { int *g2; } g1; } y;
  x[i1] = y.g1.g2;
  return(0);
}
