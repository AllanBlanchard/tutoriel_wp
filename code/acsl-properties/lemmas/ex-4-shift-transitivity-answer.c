#include <stddef.h>
#include <limits.h>

/*@
  predicate shifted{L1, L2}(int* arr, integer fst, integer last, integer shift) =
    \forall integer i ; fst <= i < last ==> \at(arr[i], L1) == \at(arr[i+shift], L2) ;

  predicate unchanged{L1, L2}(int *a, integer begin, integer end) =
    shifted{L1, L2}(a, begin, end, 0) ;

  lemma shift_ptr{L1, L2}:
    \forall int* arr, integer fst, integer last, integer s1, s2 ;
      shifted{L1, L2}(arr, fst+s1, last+s1, s2) <==> shifted{L1, L2}(arr+s1, fst, last, s2) ;

  lemma shift_transivity{L1, L2, L3}:
    \forall int* arr, integer fst, integer last, integer s1, s2 ;
    shifted{L1, L2}(arr, fst, last, s1) ==>
    shifted{L2, L3}(arr, fst+s1, last+s1, s2) ==>
      shifted{L1, L3}(arr, fst, last, s1+s2) ;
*/

/*@
  requires \valid(array+(0 .. len+shift-1)) ;
  requires shift + len <= UINT_MAX ;
  assigns array[shift .. shift+len-1];
  ensures shifted{Pre, Post}(array, 0, len, shift) ;
*/
void shift_array(int* array, size_t len, size_t shift){
  /*@
    loop invariant 0 <= i <= len ;
    loop invariant shifted{Pre, Here}(array, i, len, shift) ;
    loop invariant unchanged{Pre, Here}(array, 0, i) ;
    loop assigns i, array[shift .. shift + len - 1] ;
    loop variant i ;
  */
  for(size_t i = len ; i > 0 ; --i){
    array[i+shift-1] = array[i-1] ;
  }
}

/*@
  requires \valid(array+(0 .. len+s1+s2-1)) ;
  requires s1+s2 + len <= UINT_MAX ;
  assigns array[s1 .. s1+s2+len-1];
  ensures shifted{Pre, Post}(array, 0, len, s1+s2) ;
*/
void double_shift(int* array, size_t len, size_t s1, size_t s2){
  shift_array(array, len, s1) ;
  shift_array(array+s1, len, s2) ;
}
