
int x = 0;

typedef struct { int i; int *j;} struct1;
typedef struct { struct1 k; struct1 l;} struct2;

struct2 s = { {1, &x}, {0, &x} };

int main() {
  return(s.l.i);
}
