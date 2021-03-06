
#include <stdio.h>
#include <assert.h>

typedef struct{ int x; int a; } foo;

foo func_1(foo f)
{
  f.a = f.a + 1;
  f.x = f.a;
  return f;
}

int main()
{
  foo f0, f1;
  f0.a = 0;

  f1 = func_1(f0);
  assert(f1.a != 1);  // unsafe assertion

  return 0;
}
