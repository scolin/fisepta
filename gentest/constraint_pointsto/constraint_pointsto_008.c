
int main() {
  struct { int *f1; } x[5];
  int i1=2;
  int y[5];
  int j1=2;
  x[i1].f1 = &y[j1];
  return(0);
}

