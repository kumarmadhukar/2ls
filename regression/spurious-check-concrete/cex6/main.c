
#include <assert.h>

void foo(int x)
{
  assert(x<1);
}

int main()
{
  int y;

  while(y < 2){
    y++;
    foo(y);
  }

  return 0;
}

