
#include <assert.h>

void foo(int x)
{
  assert(x==5);
}

int main(int argc, char** argv)
{
  int y = 4;
  foo(y);

  return 0;
}

