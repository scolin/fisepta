
int main() {
  struct { struct { int *f2; } f1; } x;
  int y;
  x.f1.f2 = &y;
  return(0);
}

