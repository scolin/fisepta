
int main() {
  struct { struct { int *f2; } f1; } x;
  int *y[5][5];
  int j1 = 2;
  int j2 = 1;
  x.f1.f2 = y[j1][j2];
  return(0);
}
