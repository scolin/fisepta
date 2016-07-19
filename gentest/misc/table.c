
int a,b,c,d,e;
int *p[5];

int main() {
  int *x;
  p[0] = &a;
  p[1] = &b;
  x = (int *)p + sizeof(int *);
  int y;
  y = *x;
}
