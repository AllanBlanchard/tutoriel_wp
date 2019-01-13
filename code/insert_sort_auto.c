#include <stddef.h>
#include <limits.h>

/*@
  predicate sorted(int* a, integer b, integer e) =
    \forall integer i, j; b <= i <= j < e ==> a[i] <= a[j];
*/

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
  predicate permutation{L1, L2}(int* in, integer from, integer to) =
    \forall int v ; l_occurrences_of{L1}(v, in, from, to) ==
                    l_occurrences_of{L2}(v, in, from, to) ;
*/


/*@ 
  requires beg <= split <= end ;
  requires \valid(a + (beg .. end -1)) ;
  
  assigns \nothing ;
  
  ensures \forall int v ;
    l_occurrences_of(v, a, beg, end) ==
    l_occurrences_of(v, a, beg, split) + l_occurrences_of(v, a, split, end) ;
*/
void l_occurrences_of_explicit_split(int* a, size_t beg, size_t split, size_t end){
  /*@
    loop invariant split <= i <= end ;
    loop invariant \forall int v ; l_occurrences_of(v, a, beg, i) ==
      l_occurrences_of(v, a, beg, split) + l_occurrences_of(v, a, split, i) ;
    loop assigns i ;
    loop variant end - i ;
  */    
  for(size_t i = split ; split < end ; ++i){
    if(i == end) break ;
  }
}

/*@ 
  requires beg <= end ;
  requires \valid(a + (beg .. end -1)) ;

  assigns \nothing ;

  ensures \forall int v, size_t split ; beg <= split <= end ==>
    l_occurrences_of(v, a, beg, end) ==
    l_occurrences_of(v, a, beg, split) + l_occurrences_of(v, a, split, end) ;
*/
void l_occurrences_of_split(int* a, size_t beg, size_t end){
  /*@
    loop invariant beg <= i <= end ;
    loop invariant \forall int v, size_t split ; beg <= split < i ==>
      l_occurrences_of(v, a, beg, end) ==
      l_occurrences_of(v, a, beg, split) + l_occurrences_of(v, a, split, end) ;
    loop assigns i ;
    loop variant end - i ;
  */
  for(size_t i = beg ; i < end ; ++i){
    //@ ghost l_occurrences_of_explicit_split(a, beg, i, end);
    if(i == end) break ;
  }
}

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

  //@ ghost l_occurrences_of_split(a, beg, last+1);
  
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

  //@ ghost l_occurrences_of_explicit_split(a, beg, i, last+1);
  //@ ghost l_occurrences_of_explicit_split(a, i, i+1, last+1) ;

  /*@ ghost
    /@
      loop invariant i+1 <= j <= last+1 ;
      loop invariant \forall int v ;
        l_occurrences_of(v, a, i+1, j) ==
	l_occurrences_of{Pre}(v, a, \at(i, Here), \at(j, Here)-1) ;
      loop assigns j ;
      loop variant last  - j ;
    @/
    for(size_t j = i+1 ; j < last+1 ; ++j){
      /@ assert a[j] == \at(a[\at(j, Here)-1], Pre) ; @/
    }
  */

  /*@ assert \forall int v ; l_occurrences_of(v, a, i, last+1) == 
    l_occurrences_of(v, a, i, i+1) + l_occurrences_of(v, a, i+1, last+1) ;
  */
  /*@ assert \forall int v ; l_occurrences_of{Pre}(v, a, i, last+1) ==
    l_occurrences_of{Pre}(v, a, \at(i, Here), last) + l_occurrences_of{Pre}(v, a, last, last+1) ;
  */
  /*@ assert \forall int v ; 
    l_occurrences_of(v, a, i+1, last+1) == l_occurrences_of{Pre}(v, a, \at(i, Here), last) ;
  */
  /*@ assert \forall int v ; 
    l_occurrences_of(v, a, i, i+1) == l_occurrences_of{Pre}(v, a, last, last+1) ;
  */
  /*@ assert \forall int v ; 
      l_occurrences_of{Pre}(v, a, i, last+1) == l_occurrences_of(v, a, i, last+1) ;
  */

  /*@ ghost
    /@
      loop invariant beg <= j <= i ;
      loop invariant \forall int v ;
        l_occurrences_of(v, a, beg, j) == l_occurrences_of{Pre}(v, a, beg, \at(j, Here)) ;
      loop assigns j ;
      loop variant i - j ;
    @/
    for(size_t j = beg ; j < i ; ++j);
  */
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

    /*@ ghost
      if(i+1 < end){
        /@ loop invariant i+1 <= j <= end ;
	   loop invariant permutation{L, Here}(a, beg, j) ;
	   loop assigns j ;
	   loop variant end - j ;
	@/
        for(size_t j = i+1 ; j < end ; ++j);
      }
    */
  }
}
