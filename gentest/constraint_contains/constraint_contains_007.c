
int main() {
  int *x;
  struct { struct { int *g2; } g1; } y;
  x = y.g1.g2;
  return(0);
}
