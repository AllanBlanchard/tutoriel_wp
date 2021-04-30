#include <stdint.h>
#include <stddef.h>

/*@
  predicate shifted{L1, L2}(int* arr, integer fst, integer last, integer shift) =
    \forall integer i ; fst <= i < last ==> \at(arr[i], L1) == \at(arr[i+shift], L2) ;

  lemma shift_ptr{L1, L2}:
    \forall int* arr, integer fst, integer last, integer s1, s2 ;
      shifted{L1, L2}(arr, fst+s1, last+s1, s2) ==> shifted{L1, L2}(arr+s1, fst, last, s2) ;
*/

/*@
  requires \valid(array+(beg .. end+shift-1)) ;
  requires shift + end <= SIZE_MAX ;
  assigns array[beg+shift .. end+shift-1];
  ensures shifted{Pre, Post}(array, beg, end, shift) ;
*/
void shift_array(int* array, size_t beg, size_t end, size_t shift);

/*@
  requires \valid(array+(0 .. len+s1+s2-1)) ;
  requires s1+s2 + len <= SIZE_MAX ;
  assigns array[s1 .. s1+s2+len-1];
  ensures shifted{Pre, Post}(array+s1, 0, len, s2) ;
*/
void callee(int* array, size_t len, size_t s1, size_t s2){
  shift_array(array, s1, s1+len, s2) ;
}
