
int main() {
  struct { struct { int *f2; } f1; } x;
  struct { int *g1[5]; } y;
  int j1 = 2;
  x.f1.f2 = y.g1[j1];
  return(0);
}
