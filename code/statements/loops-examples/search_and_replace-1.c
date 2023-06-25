#include <stddef.h>

/*@
  requires \valid(array + (0 .. length-1));
  assigns array[0 .. length-1];

  ensures \forall size_t j; 0 <= j < length && \old(array[j]) == old
             ==> array[j] == new;
  ensures \forall size_t j; 0 <= j < length && \old(array[j]) != old
             ==> array[j] == \old(array[j]);
*/
void search_and_replace(int* array, size_t length, int old, int new){
  /*@
    loop invariant 0 <= i <= length;
    loop invariant \forall size_t j; i <= j < length
                     ==> array[j] == \at(array[j], Pre);
    loop invariant \forall size_t j; 0 <= j < i && \at(array[j], Pre) == old
                     ==> array[j] == new;
    loop invariant \forall size_t j; 0 <= j < i && \at(array[j], Pre) != old
                     ==> array[j] == \at(array[j], Pre);
    loop assigns i, array[0 .. length-1];
    loop variant length-i;
  */
  for(size_t i = 0; i < length; ++i){
    if(array[i] == old) array[i] = new;
  }
}
