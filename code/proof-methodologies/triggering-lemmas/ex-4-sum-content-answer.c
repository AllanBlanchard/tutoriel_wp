/* run.config
   DEPS: @PTEST_DEPS@ @PTEST_DIR@/@PTEST_NAME@.@PTEST_NUMBER@.session@PTEST_CONFIG@/interactive/*.v
   STDOPT:+"-wp-prover alt-ergo,coq -wp-session @PTEST_DIR@/@PTEST_NAME@.@PTEST_NUMBER@.session@PTEST_CONFIG@"
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

/*@
  lemma sum_separable:
    \forall int* array, integer begin, split, end ;
      begin <= split <= end ==>
        sum(array, begin, end) == sum(array, begin, split) + sum(array, split, end) ;

  lemma unchanged_sum{L1, L2}:
    \forall int* array, integer begin, end ;
      unchanged{L1, L2}(array, begin, end) ==>
        sum{L1}(array, begin, end) == sum{L2}(array, begin, end) ;
*/

/*@
  requires i < len ;
  requires array[i] < INT_MAX ;
  requires \valid(array + (0 .. len-1));
  assigns array[i];
  ensures sum(array, 0, len) == sum{Pre}(array, 0, len)+1;
*/
void inc_cell(int* array, size_t len, size_t i){
  //@ assert sum(array, 0, len) == sum(array, 0, i)+sum(array, i, len) ;
  //@ assert sum(array, i, len) == sum(array, i, i+1)+sum(array, i+1, len) ;
  array[i]++ ;
  //@ assert sum(array, 0, len) == sum(array, 0, i)+sum(array, i, len) ;
  //@ assert sum(array, i, len) == sum(array, i, i+1)+sum(array, i+1, len) ;

  //@ assert unchanged{Pre, Here}(array, 0, i);
  //@ assert unchanged{Pre, Here}(array, i+1, len);
}
