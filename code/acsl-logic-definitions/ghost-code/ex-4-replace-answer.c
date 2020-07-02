#include <stddef.h>

/*@
  requires old != new ;
  requires \valid(a + (0 .. length-1));
  requires \valid(updated + (0 .. length-1));
  requires \separated(a + (0 .. length-1), updated + (0 .. length-1));

  assigns a[0 .. length-1], updated[0 .. length-1];

  ensures \forall size_t i; 0 <= i < length && \old(a[i]) == old ==> a[i] == new;
  ensures \forall size_t i; 0 <= i < length && \old(a[i]) != old ==> a[i] == \old(a[i]);
  ensures \forall size_t i; 0 <= i < length ==> (updated[i] <==> a[i] != \old(a[i]));
*/
void replace(int* a, size_t length, int old, int new) /*@ ghost(int \ghost * updated) */ {
  /*@
    loop invariant 0 <= i <= length;
    loop invariant \forall size_t j; 0 <= j < i && \at(a[j], Pre) == old ==> a[j] == new;
    loop invariant \forall size_t j; 0 <= j < i && \at(a[j], Pre) != old ==> a[j] == \at(a[j], Pre);
    loop invariant \forall size_t j; i <= j < length ==> a[j] == \at(a[j], Pre);
    loop invariant \forall size_t j; 0 <= j < i ==> (updated[j] <==> a[j] != \at(a[j], Pre));
    loop assigns i, a[0 .. length-1], updated[0 .. length-1];
    loop variant length-i;
  */
  for(size_t i = 0 ; i < length ; ++i){
    if(a[i] == old){
      a[i] = new ;
      //@ ghost updated[i] = 1;
    } /*@ ghost else {
      updated[i] = 0;
    } */
  }
}

/*@
  requires \valid(a + (0 .. length-1));
  assigns a[0 .. length-1];
  ensures \forall integer i ; 0 <= i < length ==> -100 <= a[i] <= 100 ;
*/
void initialize(int* a, size_t length);

void caller(void){
  int a[40];
  //@ ghost int updated[40] ;

  initialize(a, 40);

  //@ ghost L: ;
  
  replace(a, 40, 0, 42) /*@ ghost(updated) */ ;

  /*@ ghost
    /@ loop invariant 0 <= i <= 40 ;
       loop assigns i;
       loop variant 40 - i ;
    @/
    for(size_t i = 0 ; i < 40 ; ++i){
      if(updated[i]){
        /@ assert a[i] != \at(a[\at(i, Here)], L); @/
      } else {
        /@ assert a[i] == \at(a[\at(i, Here)], L); @/
      }
    }
  */
}
