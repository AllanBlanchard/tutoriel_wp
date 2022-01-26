/* run.config
   OPT:
*/

#include <limits.h>
#include <stddef.h>

/*@
  axiomatic Sum_array{
    logic integer sum(int* array, integer begin, integer end) reads array[begin .. (end-1)];

    axiom empty:
      \forall int* a, integer b, e; b >= e ==> sum(a,b,e) == 0;
    axiom range:
      \forall int* a, integer b, e; b < e ==> sum(a,b,e) == sum(a,b,e-1)+a[e-1];
  }
*/

/*@
  predicate unchanged{L1, L2}(int* array, integer begin, integer end) =
    \forall integer i ; begin <= i < end ==> \at(array[i], L1) == \at(array[i], L2) ;
*/

/*@ ghost
  void sum_separable(int* array, size_t begin, size_t split, size_t end){
    // ...
  }
*/

#define unchanged_sum(_L1, _L2, _arr, _beg, _end) ;


/*@
  requires i < len ;
  requires array[i] < INT_MAX ;
  requires \valid(array + (0 .. len-1));
  assigns array[i];
  ensures sum(array, 0, len) == sum{Pre}(array, 0, len)+1;
*/
void inc_cell(int* array, size_t len, size_t i){
  // ...
  array[i]++ ;
  // ...
}
