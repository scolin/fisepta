
int main() {
  int *x[5];
  struct { int *g1; } y;
  int i1 = 2;
  x[i1] = y.g1;
  return(0);
}
