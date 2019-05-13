#include <stddef.h>
#include <limits.h>

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

/*@
  requires beg < last < UINT_MAX && \valid(a + (beg .. last));
  requires sorted(a, beg, last) ;

  assigns a[ beg .. last ] ;
  
  ensures permutation{Pre, Post}(a, beg, last+1);
  ensures sorted(a, beg, last+1) ;
*/
void insert(int* a, size_t beg, size_t last){
  size_t i = last ;
  int value = a[i] ;

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

  //@ assert rotate_left{Pre, Here}(a, i, last+1) ;
  //@ assert permutation{Pre, Here}(a, i, last+1) ;

  //@ assert unchanged{Pre, Here}(a, beg, i) ;
  //@ assert permutation{Pre, Here}(a, beg, i) ;
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
    //@ ghost L:
    insert(a, beg, i);
    //@ assert permutation{L, Here}(a, beg, i+1);
    //@ assert unchanged{L, Here}(a, i+1, end) ;
    //@ assert permutation{L, Here}(a, beg, end) ;
  }
}
