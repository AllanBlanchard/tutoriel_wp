/* run.config
   OPT:
*/

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

/*@
  lemma sum_separable:
    \forall int* array, integer begin, split, end ;
      begin <= split <= end ==> sum(array, begin, end) == 0 ; // to complete
  lemma unchanged_sum{L1, L2}:
    \forall int* array, integer begin, end ;
      unchanged{L1, L2}(array, begin, end) ==> \true ; // to complete
*/

void inc_cell(int* array, size_t len, size_t i){
  array[i]++ ;
}
