/* run.config
   OPT:
*/

/*@
  requires \valid(a + (0 .. 9)) ;
  assigns  a[0 .. 9] ;
  ensures  \forall integer j ; 0 <= j < 10 ==> a[j] == \old(a[j]) ;
*/
void foo(int a[10]){
  //@ ghost int g[10] ;
  /*@ ghost
    ; // to complete
  */

  /*@
    loop invariant 0 <= i <= 10 ;
    loop invariant \true ; // to complete
    loop assigns i, a[0 .. 9] ;
    loop variant 10 - i ;
  */
  for(int i = 0; i < 10; i++);
}
