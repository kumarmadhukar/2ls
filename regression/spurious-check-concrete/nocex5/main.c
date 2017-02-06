
#include <assert.h>

int foobar(int a){
  int i;
  if(i < a)
    return i+a;
  else
    return i-a;
}

int bar(int k){
  return (k+1);
}

void foo(int x, int s) {
  int m;
  s = foobar(m);
  x = bar(x);
  assert(x>5);
}

int main() {
  int y,k;
  __CPROVER_assume(y<100000);
  if(y > 10) foo(y,k);
  return 0;
}


