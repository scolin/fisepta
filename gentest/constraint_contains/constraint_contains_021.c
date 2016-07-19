
int main() {
  struct { int *f1; } x;
  struct { struct { int *g2; } g1; } y;
  x.f1 = y.g1.g2;
  return(0);
}
