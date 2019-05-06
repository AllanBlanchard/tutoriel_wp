#include <limits.h>
#include <stddef.h>

/*@
  predicate shifted{L1, L2}(int* arr, integer fst, integer last, integer shift) =
    \forall integer i ; fst <= i < last ==> \at(arr[i], L1) == \at(arr[i+shift], L2) ;
*/

#define shift_ptr(_L1, _L2, _arr, _fst, _last, _s1, _s2)\
  /@ assert shifted{_L1, _L2}(_arr, _fst+_s1, _last+_s1, _s2) ; @/      \
  /@ loop invariant _fst <= _i <= _last ;                               \
     loop invariant shifted{_L1, _L2}(_arr+_s1, _fst, _i, _s2) ;        \
     loop assigns _i ;                                                  \
     loop variant _last-_i ; @/                                         \
     for(size_t _i = _fst ; _i < _last ; ++_i){                         \
       /@ assert \let _h_i = \at(_i, Here) ;                            \
	  \at(_arr[_h_i+_s1], _L1) == \at(_arr[_h_i+_s1+_s2], _L2) ; @/ \
     }                                                                  \
  /@ assert shifted{_L1, _L2}(_arr+_s1, _fst, _last, _s2) ; @/


/*@
  assigns arr[fst+s1+s2 .. last+s1+s2] ;
  ensures shifted{Pre, Post}(arr, fst+s1, last+s1, s2) ;
*/
void assign_array(int* arr, size_t fst, size_t last, size_t s1, size_t s2);

/*@
  requires fst <= last ;
  requires s1+s2+last <= UINT_MAX ;
*/
void context_to_prove_shift_ptr(int* arr, size_t fst, size_t last, size_t s1, size_t s2){
 L1: ;
  assign_array(arr, fst, last, s1, s2);
 L2: ;
  //@ assert shifted{L1, L2}(arr, fst+s1, last+s1, s2) ;

  //@ ghost shift_ptr(L1, L2, arr, fst, last, s1, s2) ;

  //@ assert shifted{L1, L2}(arr+s1, fst, last, s2) ;
}


/*@
  requires \valid(array+(beg .. end+shift-1)) ;
  requires shift + end <= UINT_MAX ;
  assigns array[beg+shift .. end+shift-1];
  ensures shifted{Pre, Post}(array, beg, end, shift) ;
*/
void shift_array(int* array, size_t beg, size_t end, size_t shift);

/*@
  requires \valid(array+(0 .. len+s1+s2-1)) ;
  requires s1+s2 + len <= UINT_MAX ;
  assigns array[s1 .. s1+s2+len-1];
  ensures shifted{Pre, Post}(array+s1, 0, len, s2) ;
*/
void callee(int* array, size_t len, size_t s1, size_t s2){
  shift_array(array, s1, s1+len, s2) ;
  //@ ghost shift_ptr(Pre, Here, array, 0, len, s1, s2) ;
}
