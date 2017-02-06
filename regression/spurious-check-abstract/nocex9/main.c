#include <assert.h>

void main() 
{
  int x = 0;
  int y = 0;

  while(y<10) { x++; }

  assert(x==11);
}
