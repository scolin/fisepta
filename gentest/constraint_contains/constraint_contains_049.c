
int main() {
  struct { struct { int *f2; } f1; } x;
  struct { struct { int *g2; } g1; } y;
  x.f1.f2 = y.g1.g2;
  return(0);
}
