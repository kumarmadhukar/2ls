
#include <stdio.h>
#include <assert.h>

typedef struct{ int x; int y; int z; int w; int p; int q; int a; } foo;

foo func_1(foo f);
foo func_2(foo f);
foo func_3(foo f);
foo func_4(foo f);
foo func_5(foo f);
foo func_6(foo f);
foo func_7(foo f);
foo func_8(foo f);

foo func_1(foo f)
{
  f.x = 23 + 12;
  f.x = 4 - 1;
  if(f.w > f.x) {f.q = 21 * f.z;} else {f.q = 4 / f.p;}
  f.a = f.a + 1;
  f.z = f.y * f.x;
  f.x = 11 - f.p;
  f.y = 1 - 19;
  f.y = f.w - 14;
  return f;
}

/**********************************************************************/

foo func_2(foo f)
{
  if(f.y < f.q) {f.x = f.w / 24;} else {f.w = 18 / 3;}
  f.w = f.p * f.q;
  if(f.q < 6) {f.y = 25 - f.x;} else {f.q = f.y / f.w;}
  f.a = f.a + 1;
  if(f.x <= f.x) {f.z = 9 + f.x;} else {f.y = 1 + f.x;}
  f.x = f.q / 25;
  f.w = f.x - f.y;
  f.x = 9 + f.y;
  f.y = 24 - 2;
  f.w = 10 + f.z;
  return f;
}

/**********************************************************************/

foo func_3(foo f)
{
  if(f.p == 12) {f.w = 22 + 7;} else {f.p = f.x + f.q;}
  f.y = f.p + f.x;
  f.w = 6 * f.y;
  if(f.z <= 20) {f.q = 21 / 24;} else {f.w = f.q * f.w;}
  f.w = f.y - 10;
  f.q = 2 - 20;
  f.x = f.x / 10;
  f.p = 16 * 23;
  f.w = 18 - 13;
  f.w = f.p - 2;
  f.z = 7 + f.w;
  f.a = f.a + 1;
  f.x = 16 / f.x;
  return f;
}

/**********************************************************************/

foo func_4(foo f)
{
  f.w = f.y + f.y;
  f.q = 18 * 13;
  f.y = f.z * f.y;
  f.x = 1 * 25;
  f.y = 4 / f.q;
  f.x = f.p / 9;
  f.a = f.a + 1;
  if(f.x >= 7) {f.q = f.q / 8;} else {if(f.x < 9) {f.z = 16 + f.p;} else {f.x = f.w - 18;}}
  f.y = 2 * 4;
  f.q = 16 + f.x;
  f.q = 16 * f.w;
  if(f.w > 14) {f.q = 20 + 20;} else {f.x = 25 + 9;}
  return f;
}

/**********************************************************************/

foo func_5(foo f)
{
  f.a = f.a + 1;
  if(f.x == 13) {f.p = 13 * f.x;} else {f.w = f.q / f.w;}
  f.y = 21 * f.x;
  f.p = 4 * 25;
  if(f.p >= 24) {f.x = 11 * 6;} else {f.p = 9 * f.p;}
  f.x = 3 + f.z;
  f.x = f.x + 22;
  f.z = 8 / 8;
  f.q = 18 + f.x;
  f.x = 5 * f.z;
  f.y = f.w + f.w;
  return f;
}

/**********************************************************************/

foo func_6(foo f)
{
  f.y = f.w / f.q;
  f.p = f.x + 8;
  f.a = f.a + 1;
  f.z = f.w * 20;
  if(f.x < f.p) {f.x = f.z + 2;} else {f.y = f.y * f.x;}
  if(f.y <= f.y) {f.q = f.y * f.w;} else {f.q = f.w - 13;}
  f.p = 9 + f.y;
  f.q = f.y / 14;
  f.p = 18 / f.z;
  if(f.w < f.p) {f.w = 17 * f.p;} else {f.p = f.y - 10;}
  f.p = 3 / 14;
  f.q = 10 - f.w;
  if(f.y > 12) {f.z = f.q - 24;} else {f.x = f.z / 17;}
  return f;
}

/**********************************************************************/

foo func_7(foo f)
{
  f.q = f.q * 23;
  f.w = 25 - f.w;
  if(f.q < f.y) {f.w = 21 + f.z;} else {f.p = 16 - 1;}
  f.y = f.z * f.z;
  f.x = 5 * 16;
  f.x = 11 + f.x;
  f.z = f.y - f.y;
  f.q = 11 - f.z;
  f.a = f.a + 1;
  return f;
}

/**********************************************************************/

foo func_8(foo f)
{
  f.w = f.y - 15;
  f.q = f.x + f.z;
  f.y = 5 / 1;
  if(f.q < 3) {f.p = 6 * f.x; } else {f.w = 8 + 21;} 
  f.p = 19 / f.p;
  f.z = 4 / f.z;
  if(f.x < 12) {f.p = f.y - 4; } else {f.x = 15 + 2;} 
  f.q = 19 / f.w;
  if(f.p > 24) {f.z = 5 / 9;} else {f.w = f.x + f.z;}
  f.z = f.z + 1;
  f.a = f.a + 1;
  if(f.z > f.y) {f.y = f.y + f.x;} else {f.y = 13 - 18;}
  return f;
}


/**********************************************************************/

int main()
{
  foo f0, f1, f2, f3, f4, f5, f6, f7, f8;

//  __CPROVER_assume((f0.a >= 0) && (f0.a <= 9));
  f0.a = 0;

  f1 = func_1(f0);
/*  f2 = func_2(f1);
  f3 = func_3(f2);
  f4 = func_4(f3);
  f5 = func_5(f4);
  f6 = func_6(f5);
  f7 = func_7(f6);
  f8 = func_8(f7);*/

  assert(/*(f8.x + f8.y + f8.z + f8.w + f8.p + f8.q > 0) &&*/ (f1.a != 1));  // unsafe assertion

  return 0;
}
