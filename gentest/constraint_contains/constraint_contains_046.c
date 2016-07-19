
int main() {
  struct { struct { int *f2; } f1; } x;
  struct { int *g1; } y[5];
  int j1 = 2;
  x.f1.f2 = y[j1].g1;
  return(0);
}
