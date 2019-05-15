/*@
  ensures \result == \old(a) + 10;
*/
int add_ten(int a){
  /*@
    loop invariant 0 <= i <= 10;
    loop assigns i, a;
    loop variant 10 - i;
  */
  for (int i = 0; i < 10; ++i)
    ++a;

  return a;
}
