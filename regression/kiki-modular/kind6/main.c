
#include <assert.h>

int inc(int c)
{
  return c+1;
}

int dec(int b)
{
  return b-1;
}

int add(int i, int j)
{
  int b = i;
  int c = j;
  int ret = c;

  while(b > 0){
    b = dec(b);
    c = inc(c);
    ret = c;
    assert((ret + b)  == (i + j)); //loop invariant
  }
  assert(ret == (i + j));
  return ret;
}

void main() {
  int x = 5;
  int y = 3;
  int result = add(x, y);
}
