
int main() {
  int *x;
  struct { int *g1; } y;
  x = y.g1;
  return(0);
}
