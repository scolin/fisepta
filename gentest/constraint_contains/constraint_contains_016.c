
int main() {
  struct { int *f1; } x;
  int *y[5];
  int j1 = 2;
  x.f1 = y[j1];
  return(0);
}
