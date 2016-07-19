
int x;
int y;

int main(int argc, char **argv) {
  int *z;
  z = (argc++ > 10 && argc++ < 20) ? &x : &y;
  return(0);
}
