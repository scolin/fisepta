
int main() {
  struct { int *f1[5]; } x;
  int i1=2;
  int y[5];
  int j1=2;
  x.f1[i1] = &y[j1];
  return(0);
}

