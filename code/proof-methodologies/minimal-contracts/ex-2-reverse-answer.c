#include <stddef.h>

/*@
  requires \valid(a) && \valid(b);
  assigns *a, *b;
*/
void swap(int* a, int* b){
  int tmp = *a;
  *a = *b;
  *b = tmp;
}

/*@
  requires \valid(array + (0 .. len-1)) ;
  assigns array[0 .. len-1];
*/
void reverse(int* array, size_t len){
  /*@
    loop invariant 0 <= i <= len/2 ;
    loop assigns i, array[0 .. len-1] ;
    loop variant len-i ;
  */
  for(size_t i = 0 ; i < len/2 ; ++i){
    swap(array+i, array+len-i-1) ;
  }
}
