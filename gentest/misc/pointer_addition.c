
int *t[5];

int main() {
  int x;
  int *p_x;
  t[3] = &x;
  p_x = *(t + 3*sizeof(int *));
  return(0);
}
