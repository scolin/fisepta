
int main() {
  struct { int *f1; } x[5];
  int i1=2;
  int y;
  x[i1].f1 = &y;
  return(0);
}

