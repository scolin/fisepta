
int main() {
  struct { int *f1; } x;
  struct { int *g1; } y;
  x.f1 = y.g1;
  return(0);
}
