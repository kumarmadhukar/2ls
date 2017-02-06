#include <assert.h>

void main() 
{
  int x = 0;
  int y = 0;
  int c;

  while(x<10) ++x;

  int c;
  while(c) ++y;

  assert(x==10);
}
