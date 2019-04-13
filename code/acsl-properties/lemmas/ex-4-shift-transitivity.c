#include <stddef.h>
#include <limits.h>

/*@
  // predicate shifted{L1, L2}(int* arr, integer fst, integer last, integer shift) =
  // ...

  // predicate unchanged{L1, L2}(int *a, integer begin, integer end) =
  // ...

  // lemma shift_ptr{...}:
  // ...

  // lemma shift_transivity{...}:
  // ...
*/

void shift_array(int* array, size_t len, size_t shift){
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
