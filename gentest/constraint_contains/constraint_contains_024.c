
int main() {
  struct { int *f1; } x[5];
  int i1 = 2;
  struct { int *g1; } y;
  x[i1].f1 = y.g1;
  return(0);
}
