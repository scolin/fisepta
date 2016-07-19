
int main() {
  struct { int *f1[5]; } x;
  int i1=2;
  int y;
  x.f1[i1] = &y;
  return(0);
}

