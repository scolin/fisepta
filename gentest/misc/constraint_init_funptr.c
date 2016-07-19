
int add(int x, int y) {
  return(x+y);
}

typedef int (*binop)(int,int);

binop f = add;

int main() {
  int a = 42;
  int b = 66;
  int c = f(a,b);
  return(c);
}
