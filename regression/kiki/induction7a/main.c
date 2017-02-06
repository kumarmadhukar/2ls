void main()
{
  int s=0;
  int x=0;
  while(1)
  {
    s += 2;
    if(x==1) s++; 
    x++;
    assert(s == 2*x);
  }
}
