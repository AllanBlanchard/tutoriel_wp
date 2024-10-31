/*@ ghost
	/@ requires 0 <= length;
     requires \valid_read(original+(0 .. length-1));
     requires \valid(copy+(0 .. length-1));
     requires \separated(original+(0 .. length-1), copy+(0 .. length-1));
     assigns copy[0 .. length-1];
     ensures \forall integer j ; 0 <= j < length ==> original[j] == copy[j] ;
  @/
	void copy(int *original, int \ghost * copy, int length){
    /@ loop invariant 0 <= i <= length ;
       loop invariant \forall integer j ; 0 <= j < i ==> original[j] == copy[j] ;
       loop assigns i, copy[0 .. length-1];
       loop variant length - i ; @/
    for(int i = 0 ; i < length ; ++i){
      copy[i] = original[i];
    }
  }
*/

/*@
  requires \valid(a + (0 .. 9)) ;
  assigns  a[0 .. 9] ;
  ensures  \forall integer j ; 0 <= j < 10 ==> a[j] == \old(a[j]) ;
*/
void foo(int a[10]){
  //@ ghost int g[10] ;
	//@ ghost copy(a, g, 10);

  /*@
    loop invariant 0 <= i <= 10 ;
    loop invariant \forall integer j ; 0 <= j < 10 ==> a[j] == g[j] ;
    loop assigns i, a[0 .. 9] ;
    loop variant 10 - i ;
  */
  for(int i = 0; i < 10; i++);
}
