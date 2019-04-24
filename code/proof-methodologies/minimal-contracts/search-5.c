#include <stddef.h>
#include <limits.h>

/*@
  requires \valid_read(array + (0 .. length-1)) ;
  assigns \nothing ;
  ensures \result == NULL ||
          (\exists integer i ; 0 <= i < length && array+i == \result) ;
*/
int* search(int* array, size_t length, int element){
  /*@
    loop invariant 0 <= i <= length ;
    loop assigns i ;
    loop variant length - i ;
  */
  for(size_t i = 0; i < length; i++)
    if(array[i] == element) return &array[i];
  return NULL;
}

/*@
  requires \forall integer i ; 0 <= i < length ==> array[i] < INT_MAX ;
  requires \valid(array + (0 .. length-1)) ;
*/
void foo(int *array, size_t length){
  int *p = search(array,length,0);
  if (p){
    *p += 1 ;
  }
}
