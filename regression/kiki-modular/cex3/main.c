
#include <assert.h>

int foo(int x)
{
  assert(x!=5);
}

int main(int argc, char** argv)
{
  int y;
  if(y > 0) foo(y);

  return 0;
}

