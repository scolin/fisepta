
int main() {
  int *x;
  struct { int *g1; } y[5];
  int j1 = 2;
  x = y[j1].g1;
  return(0);
}
