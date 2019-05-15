#include <stddef.h>

/*@
  predicate replaced{L1, L2}(int *a, integer begin, integer end, int old, int new) =
    \forall integer i ; begin <= i < end ==> (
      (\at(a[i], L1) == old ==> \at(a[i], L2) == new) &&
      (\at(a[i], L1) != old ==> \at(a[i], L2) == \at(a[i], L1))) ;
*/
/*@
  predicate replaced{L1, L2}(int *a, integer length, int old, int new) =
    replaced{L1, L2}(a, 0, length, old, new) ;
*/
/*@
  predicate unchanged{L1, L2}(int *a, integer begin, integer end) =
    \forall integer i ; begin <= i < end ==> \at(a[i], L1) == \at(a[i], L2) ;
*/

/*@
  requires \valid(array + (0 .. length-1));
  assigns array[0 .. length-1];
  ensures replaced{Pre, Post}(array, length, old, new);
*/
void search_and_replace(int* array, size_t length, int old, int new){
  /*@
    loop invariant 0 <= i <= length;
    loop invariant replaced{Pre, Here}(array, i, old, new);
    loop invariant unchanged{Pre, Here}(array, i, length);
    loop assigns i, array[0 .. length-1];
    loop variant length-i;
  */
  for(size_t i = 0; i < length; ++i){
    if(array[i] == old) array[i] = new;
  }
}
