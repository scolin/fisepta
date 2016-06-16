// #include <stdarg.h>

int *glob;

int variadic(int *x, ...) {
  __builtin_va_list args;
  __builtin_va_start(args, x);
  glob = __builtin_va_arg(args, int *);
  return(*x);
} 

int main() {
  int a, b, c;
  variadic(&a, &b, &c);
  return(c);
}
