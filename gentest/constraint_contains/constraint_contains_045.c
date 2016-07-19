
int main() {
  struct { struct { int *f2; } f1; } x;
  struct { int *g1; } y;
  x.f1.f2 = y.g1;
  return(0);
}
