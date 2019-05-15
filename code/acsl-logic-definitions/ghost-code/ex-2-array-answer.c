/*@
  requires \valid(a + (0 .. 9)) ;
  assigns  a[0 .. 9] ;
  ensures  \forall integer j ; 0 <= j < 10 ==> a[j] == \old(a[j]) ;
*/
void foo(int a[10]){
  //@ ghost int g[10] ;
  /*@ ghost
    /@
     loop invariant 0 <= i <= 10 ;
     loop invariant \forall integer j ; 0 <= j < i ==> a[j] == g[j] ;
     loop assigns i, g[0 .. 9];
     @/
    for(int i = 0 ; i < 10 ; ++i){
      g[i] = a[i];
    }
  */
  
  /*@
    loop invariant 0 <= i <= 10 ;
    loop invariant \forall integer j ; 0 <= j < 10 ==> a[j] == g[j] ;
    loop assigns i, a[0 .. 9] ;
    loop variant 10 - i ;
  */
  for(int i = 0; i < 10; i++);
}
