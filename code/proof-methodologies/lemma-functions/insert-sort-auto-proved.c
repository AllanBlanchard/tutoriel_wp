/* run.config
   STDOPT:+"-warn-unsigned-overflow -warn-unsigned-downcast -wp-timeout 20"
*/

#include <stddef.h>
#include <stdint.h>

/*@
  axiomatic Occurrences_Axiomatic{
    logic integer l_occurrences_of{L}(int value, int* in, integer from, integer to)
      reads in[from .. to-1];

    axiom occurrences_empty_range{L}:
      \forall int v, int* in, integer from, to;
        from >= to ==> l_occurrences_of{L}(v, in, from, to) == 0;

    axiom occurrences_positive_range_with_element{L}:
      \forall int v, int* in, integer from, to;
        (from < to && in[to-1] == v) ==>
      l_occurrences_of(v,in,from,to) == 1+l_occurrences_of(v,in,from,to-1);

    axiom occurrences_positive_range_without_element{L}:
      \forall int v, int* in, integer from, to;
        (from < to && in[to-1] != v) ==>
      l_occurrences_of(v,in,from,to) == l_occurrences_of(v,in,from,to-1);
  }
*/

/*@
  predicate sorted(int* a, integer b, integer e) =
    \forall integer i, j; b <= i <= j < e ==> a[i] <= a[j];

  predicate shifted{L1, L2}(integer s, int* a, integer beg, integer end) =
    \forall integer k ; beg <= k < end ==> \at(a[k], L1) == \at(a[s+k], L2) ;

  predicate unchanged{L1, L2}(int* a, integer beg, integer end) =
    shifted{L1, L2}(0, a, beg, end);

  predicate rotate_left{L1, L2}(int* a, integer beg, integer end) =
    beg < end && \at(a[beg], L2) == \at(a[end-1], L1) &&
    shifted{L1, L2}(1, a, beg, end - 1) ;

  predicate permutation{L1, L2}(int* in, integer from, integer to) =
    \forall int v ; l_occurrences_of{L1}(v, in, from, to) ==
                    l_occurrences_of{L2}(v, in, from, to) ;
*/
/*@ lemma transitive_permutation{L1, L2, L3}:
  \forall int* a, integer beg, integer end ;
    permutation{L1, L2}(a, beg, end) ==>
    permutation{L2, L3}(a, beg, end) ==>
      permutation{L1, L3}(a, beg, end) ;
*/
/*@ lemma one_same_element_same_count{L1, L2}:
  \forall int* a, int* b, int v, integer pos_a, pos_b ;
    \at(a[pos_a], L1) == \at(b[pos_b], L2) ==>
    l_occurrences_of{L1}(v, a, pos_a, pos_a+1) ==
    l_occurrences_of{L2}(v, b, pos_b, pos_b+1) ;
*/


/*@ ghost
  /@
    requires beg <= split <= end ;

    assigns \nothing ;

    ensures \forall int v ;
      l_occurrences_of(v, a, beg, end) ==
      l_occurrences_of(v, a, beg, split) + l_occurrences_of(v, a, split, end) ;
  @/
  void l_occurrences_of_explicit_split(int* a, size_t beg, size_t split, size_t end){
    /@
      loop invariant split <= i <= end ;
      loop invariant \forall int v ; l_occurrences_of(v, a, beg, i) ==
        l_occurrences_of(v, a, beg, split) + l_occurrences_of(v, a, split, i) ;
      loop assigns i ;
      loop variant end - i ;
    @/
    for(size_t i = split ; i < end ; ++i);
  }
*/

/*@ ghost
  /@
    requires beg <= end ;

    assigns \nothing ;

    ensures \forall int v, size_t split ; beg <= split <= end ==>
      l_occurrences_of(v, a, beg, end) ==
      l_occurrences_of(v, a, beg, split) + l_occurrences_of(v, a, split, end) ;
  @/
  void l_occurrences_of_split(int* a, size_t beg, size_t end){
    /@
      loop invariant beg <= i <= end ;
      loop invariant \forall int v, size_t split ; beg <= split < i ==>
        l_occurrences_of(v, a, beg, end) ==
        l_occurrences_of(v, a, beg, split) + l_occurrences_of(v, a, split, end) ;
      loop assigns i ;
      loop variant end - i ;
    @/
    for(size_t i = beg ; i < end ; ++i){
      l_occurrences_of_explicit_split(a, beg, i, end);
    }
  }
*/

/*@ ghost
  /@
    requires beg < end ;

    assigns \nothing ;

    ensures \forall int v, size_t any ; beg <= any < end ==>
      l_occurrences_of(v, a, any, end) ==
      l_occurrences_of(v, a, any, end-1) + l_occurrences_of(v, a, end-1, end) ;
  @/
  void l_occurrences_of_from_any_split_last(int* a, size_t beg, size_t end){
    /@
      loop invariant beg <= i <= end-1 ;
      loop invariant \forall int v, size_t j ;
        beg <= j < i ==>
        l_occurrences_of(v, a, j, end) ==
        l_occurrences_of(v, a, j, end-1) + l_occurrences_of(v, a, end-1, end) ;
      loop assigns i ;
      loop variant (end - 1) - i ;
    @/
    for(size_t i = beg ; i < end-1 ; ++i){
      l_occurrences_of_explicit_split(a, i, end-1, end);
    }
  }
*/


#define unchanged_permutation(_L1, _L2, _arr, _fst, _last)      \
  /@ assert unchanged{_L1, _L2}(_arr, _fst, _last) ; @/         \
  /@ loop invariant _fst <= _i <= _last ;                       \
     loop invariant permutation{_L1, _L2}(_arr, _fst, _i) ;     \
     loop assigns _i ;                                          \
     loop variant _last - _i ;                                  \
   @/                                                           \
   for(size_t _i = _fst ; _i < _last ; ++_i) ;                  \
   /@ assert permutation{_L1, _L2}(_arr, _fst, _last); @/


/*@
  assigns arr[fst .. last-1] ;
  ensures unchanged{Pre, Post}(arr, fst, last);
*/
void unchanged_permutation_premise(int* arr, size_t fst, size_t last);

/*@
  requires fst <= last ;
*/
void context_to_prove_unchanged_permutation(int* arr, size_t fst, size_t last){
 L1: ;
  unchanged_permutation_premise(arr, fst, last);
 L2: ;
  //@ ghost unchanged_permutation(L1, L2, arr, fst, last) ;

  //@ assert permutation{L1, L2}(arr, fst, last) ;
}

#define rotate_left_permutation(_L1, _L2, _arr, _fst, _last)            \
  /@ assert rotate_left{_L1, _L2}(_arr, _fst, _last) ; @/               \
  /@ loop invariant _fst+1 <= _i <= _last ;                             \
     loop invariant \forall int _v ;                                    \
       l_occurrences_of{_L1}(_v, _arr, _fst, \at(_i-1, Here)) ==        \
       l_occurrences_of{_L2}(_v, _arr, _fst+1, \at(_i, Here)) ;         \
     loop assigns _i ;                                                  \
     loop variant _last - _i ;                                          \
   @/                                                                   \
   for(size_t _i = _fst+1 ; _i < _last ; ++_i) {                        \
     /@ assert \at(_arr[\at(_i-1, Here)], _L1) ==                       \
               \at(_arr[\at(_i, Here)], _L2) ;                          \
     @/                                                                 \
   }                                                                    \
   l_occurrences_of_explicit_split(_arr, _fst, _fst+1, _last) ;         \
   /@ assert \forall int _v ;                                           \
     l_occurrences_of{_L1}(_v, _arr, _fst, _last) ==                    \
       l_occurrences_of{_L1}(_v, _arr, _fst, _last-1) +                 \
       l_occurrences_of{_L1}(_v, _arr, _last-1, _last) ;                \
   @/                                                                   \
   /@ assert \at(_arr[_fst], _L2) == \at(_arr[_last-1], _L1) ==>        \
     (\forall int _v ;                                                  \
       l_occurrences_of{_L2}(_v, _arr, _fst, _fst+1) ==                 \
       l_occurrences_of{_L1}(_v, _arr, _last-1, _last)) ;               \
   @/                                                                   \
   /@ assert permutation{_L1, _L2}(_arr, _fst, _last); @/

/*@
  assigns arr[fst .. last-1] ;
  ensures rotate_left{Pre, Post}(arr, fst, last);
*/
void rotate_left_permutation_premise(int* arr, size_t fst, size_t last);

/*@
  requires fst < last ;
*/
void context_to_prove_rotate_left_permutation(int* arr, size_t fst, size_t last){
 L1: ;
  //@ ghost l_occurrences_of_explicit_split(arr, fst, last-1, last) ;
  rotate_left_permutation_premise(arr, fst, last);
 L2: ;
  //@ ghost rotate_left_permutation(L1, L2, arr, fst, last) ;

  //@ assert permutation{L1, L2}(arr, fst, last) ;
}

/*@
  requires beg < last < SIZE_MAX && \valid(a + (beg .. last));
  requires sorted(a, beg, last) ;

  assigns a[ beg .. last ] ;

  ensures permutation{Pre, Post}(a, beg, last+1);
  ensures sorted(a, beg, last+1) ;
*/
void insert(int* a, size_t beg, size_t last){
  size_t i = last ;
  int value = a[i] ;

  //@ ghost l_occurrences_of_split(a, beg, last+1);
  //@ ghost l_occurrences_of_from_any_split_last(a, beg, last+1);

  /*@
    loop invariant beg <= i <= last ;
    loop invariant \forall integer k ; i <= k < last ==> a[k] > value ;
    loop invariant \forall integer k ; beg <= k <= i    ==> a[k] == \at(a[k], Pre) ;
    loop invariant \forall integer k ; i+1 <= k <= last ==> a[k] == \at(a[k-1], Pre) ;

    loop assigns i, a[beg .. last] ;
    loop variant i ;
  */
  while(i > beg && a[i - 1] > value){
    a[i] = a[i - 1] ;
    --i ;
  }
  a[i] = value ;
  //@ assert sorted(a, beg, last+1) ;

  /*@ assert
      \forall int v ;
      l_occurrences_of{Pre}(v, a, \at(i, Here), last+1) ==
        l_occurrences_of{Pre}(v, a, \at(i, Here), last) +
        l_occurrences_of{Pre}(v, a, last, last +1);
  */

  //@ assert rotate_left{Pre, Here}(a, i, last+1) ;
  //@ ghost rotate_left_permutation(Pre, Here, a, i, last+1) ;
  //@ assert permutation{Pre, Here}(a, i, last+1) ;

  //@ assert unchanged{Pre, Here}(a, beg, i) ;
  //@ ghost unchanged_permutation(Pre, Here, a, beg, i) ;
  //@ assert permutation{Pre, Here}(a, beg, i) ;

  //@ ghost l_occurrences_of_explicit_split(a, beg, i, last+1);
}


/*@
  requires beg < end && \valid(a + (beg .. end-1));
  assigns a[beg .. end-1];
  ensures sorted(a, beg, end);
  ensures permutation{Pre, Post}(a,beg,end);
*/
void insertion_sort(int* a, size_t beg, size_t end){
  /*@
    loop invariant beg+1 <= i <= end ;
    loop invariant sorted(a, beg, i) ;
    loop invariant permutation{Pre, Here}(a,beg,end);
    loop assigns a[beg .. end-1], i ;
    loop variant end-i ;
  */
  for(size_t i = beg+1; i < end; ++i) {
    //@ ghost L: ;
    insert(a, beg, i);
    //@ ghost PI: ;
    //@ assert permutation{L, PI}(a, beg, i+1);
    //@ assert unchanged{L, PI}(a, i+1, end) ;
    /*@ ghost
      if(i+1 < end){
        /@ loop invariant i+1 <= j <= end ;
           loop invariant permutation{L, PI}(a, beg, j) ;
           loop assigns j ;
           loop variant end - j ;
        @/
        for(size_t j = i+1 ; j < end ; ++j);
      }
    */
  }
}
