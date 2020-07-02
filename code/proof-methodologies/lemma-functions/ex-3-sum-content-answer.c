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
  /@
    requires begin <= split <= end ;
    assigns  \nothing ;
    ensures  sum(array, begin, end) == sum(array, begin, split) + sum(array, split, end) ;
  @/
  void sum_separable(int* array, size_t begin, size_t split, size_t end){
    /@
      loop invariant split <= i <= end ;
      loop invariant 
        sum(array, begin, i) == sum(array, begin, split) + sum(array, split, i) ;
      loop assigns i ;
      loop variant end - i ;
    @/
    for(size_t i = split ; i < end ; ++i);
  }
*/

#define unchanged_sum(_L1, _L2, _arr, _beg, _end)                       \
  /@ assert unchanged{_L1, _L2}(_arr, _beg, _end) ; @/                  \
  /@ loop invariant _beg <= _i <= _end ;                                \
     loop invariant sum{_L1}(_arr, _beg, _i) ==                         \
                    sum{_L2}(_arr, _beg, _i) ;                          \
     loop assigns _i ;                                                  \
     loop variant _end - _i ;                                           \
   @/                                                                   \
  for(size_t _i = _beg ; _i < _end ; ++_i) ;                            \
  /@ assert sum{_L1}(_arr, _beg, _end) == sum{_L2}(_arr, _beg, _end) ; @/


/*@
  requires i < len ;
  requires array[i] < INT_MAX ;
  requires \valid(array + (0 .. len-1));
  assigns array[i];
  ensures sum(array, 0, len) == sum{Pre}(array, 0, len)+1;
*/
void inc_cell(int* array, size_t len, size_t i){
  //@ ghost sum_separable(array, 0, i, len);
  //@ ghost sum_separable(array, i, i+1, len);
  array[i]++ ;
  //@ ghost sum_separable(array, 0, i, len);
  //@ ghost sum_separable(array, i, i+1, len);
  
  //@ ghost unchanged_sum(Pre, Here, array, 0, i);
  //@ ghost unchanged_sum(Pre, Here, array, i+1, len);
}
