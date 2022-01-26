/* run.config
   OPT:
*/

/*@
  requires x >= 0 ;
  assigns  \nothing ;
  ensures  \result == 2 * x ;
*/
int times_2(int x){
  int r = 0 ;
  /*@
    loop invariant 0 <= x ;
    loop invariant r == 0 ; // to complete
    loop invariant \true ; // to complete
  */
  while(x > 0){
    r += 2 ;
    x -- ;
  }
  return r;
}
