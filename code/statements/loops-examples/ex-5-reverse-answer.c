#include <stddef.h>

/*@
  requires \valid(a) && \valid(b);
  assigns *a, *b;
  ensures  *a == \old(*b) && *b == \old(*a);
*/
void swap(int* a, int* b){
  int tmp = *a;
  *a = *b;
  *b = tmp;
}

/*@
  requires \valid(array + (0 .. len-1)) ;

  assigns array[0 .. len-1];

  ensures \forall integer j ; 0 <= j < len ==> array[j] == \old(array[len-j-1]);
*/
void reverse(int* array, size_t len){
  /*@
    loop invariant 0 <= i <= len/2 ;
    loop invariant 
      \forall integer j ; (0 <= j < i || len-i <= j < len) ==> 
        array[j] == \at(array[len-j-1], Pre);
    loop invariant
      \forall integer j ; i <= j < len-i ==> array[j] == \at(array[j], Pre);
    loop assigns i, array[0 .. len-1] ;
    loop variant len-i ;
  */
  for(size_t i = 0 ; i < len/2 ; ++i){
    swap(array+i, array+len-i-1) ;
  }
}
