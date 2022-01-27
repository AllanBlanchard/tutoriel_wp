/* run.config
   STDOPT:+"-wp-prover alt-ergo,coq -wp-session @PTEST_SUITE_DIR@/oracle@PTEST_CONFIG@/@PTEST_NAME@.session"
*/

#include <stdint.h>
#include <stddef.h>

/*@
  predicate sorted(int* arr, integer begin, integer end) =
    \forall integer i, j ; begin <= i <= j < end ==> arr[i] <= arr[j] ;

  predicate in_array(int value, int* arr, integer begin, integer end) =
    \exists integer j ; begin <= j < end && arr[j] == value ;
*/

/*@
  requires \valid_read(arr + (beg .. end-1));
  requires sorted(arr, beg, end) ;
  requires beg <= end ;

  assigns \nothing ;

  behavior exists:
    assumes in_array(value, arr, beg, end);
    ensures beg <= \result < end && arr[\result] == value ;

  behavior does_not_exists:
    assumes !in_array(value, arr, beg, end);
    ensures \result == end ;

  complete behaviors ;
  disjoint behaviors ;
*/
size_t bsearch(int* arr, size_t beg, size_t end, int value){
  if(end == beg) return end ;

  size_t low = beg ;
  size_t up = end ;

  /*@
    loop invariant beg <= low && up <= end ;
    loop invariant
      \forall integer i ; beg <= i < end && arr[i] == value ==> low <= i < up ;
    loop assigns low, up ;
    loop variant up - low ;
  */
  while(low < up){
    size_t mid = low + (up - low)/2 ;
    if     (arr[mid] > value) up = mid ;
    else if(arr[mid] < value) low = mid+1 ;
    else return mid ;
  }
  return end ;
}

/*@
  predicate shifted_cell{L1, L2}(int* p, integer shift) =
    \at(p[0], L1) == \at(p[shift], L2) ;

  predicate shifted{L1, L2}(int* arr, integer fst, integer last, integer shift) =
    \forall integer i ; fst <= i < last ==> shifted_cell{L1, L2}(arr+i, shift) ;

  predicate unchanged{L1, L2}(int *a, integer begin, integer end) =
    shifted{L1, L2}(a, begin, end, 0) ;
*/

/*@
  requires \valid(array+(0 .. len+shift-1)) ;
  requires shift + len <= SIZE_MAX ;
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
  lemma shifted_still_sorted{L1, L2}:
    \forall int* array, integer len, integer shift ;
      sorted{L1}(array, 0, len) ==>
      shifted{L1, L2}(array, 0, len, shift) ==>
        sorted{L2}(array, shift, shift+len) ;
*/
/*@
  lemma in_array_shifted{L1, L2}:
    \forall int* array, integer len, integer shift, int value ;
      in_array{L1}(value, array, 0, len) ==>
      shifted{L1, L2}(array, 0, len, shift) ==>
        in_array{L2}(value, array, shift, shift+len) ;
*/

/*@
  requires len < SIZE_MAX ;
  requires sorted(array, 0, len) ;
  requires \valid(array + (0 .. len));
  requires in_array(value, array, 0, len) ;

  assigns array[1 .. len] ;

  ensures 1 <= \result <= len ;
*/
size_t shift_and_search(int* array, size_t len, int value){
  shift_array(array, len, 1);
  return bsearch(array, 1, len+1, value);
}
