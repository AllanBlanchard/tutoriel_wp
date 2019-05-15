#include <stddef.h>
#include <limits.h>

/*@ predicate sorted(int* arr, integer end) =
      \forall integer i, j ; 0 <= i <= j < end ==> arr[i] <= arr[j] ;
    predicate element_level_sorted(int* array, integer end) =
      \forall integer i ; 0 <= i < end-1 ==> array[i] <= array[i+1] ; 
*/

/*@ requires \valid_read(arr + (0 .. len-1));
    requires sorted(arr, len) ;
*/
size_t bsearch(int* arr, size_t len, int value);


#define element_level_sorted_implies_sorted(_arr, _len) \
  /@ assert element_level_sorted(_arr, _len) ; @/       \
  /@ loop invariant 0 <= _i <= _len ;                   \
     loop invariant sorted(_arr, _i) ;                  \
     loop assigns _i ;                                  \
     loop variant _len-_i ; @/                          \
  for(size_t _i = 0 ; _i < _len ; ++_i){                \
    /@ assert 0 < _i ==> _arr[_i-1] <= _arr[_i] ; @/    \
  }                                                     \
  /@ assert sorted(_arr, _len); @/

/*@ requires \valid_read(arr + (0 .. len-1));
    requires element_level_sorted(arr, len) ;
*/
unsigned bsearch_callee(int* arr, size_t len, int value){
  //@ ghost element_level_sorted_implies_sorted(arr, len) ;
  return bsearch(arr, len, value);
}
