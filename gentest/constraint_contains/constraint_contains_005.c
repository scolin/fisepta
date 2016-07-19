
int main() {
  int *x;
  struct { int *g1[5]; } y;
  int j1 = 2;
  x = y.g1[j1];
  return(0);
}
