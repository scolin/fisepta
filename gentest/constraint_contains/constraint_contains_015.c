
int main() {
  struct { int *f1; } x;
  int *y;
  x.f1 = y;
  return(0);
}
