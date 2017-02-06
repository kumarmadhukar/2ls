#include <assert.h>

int inc(int x)
{
  return x+1;
}

void main() 
{
  int x = 0;
  int y = 0;

  x = inc(x);
  y = inc(y);

  assert(x==1);
}
