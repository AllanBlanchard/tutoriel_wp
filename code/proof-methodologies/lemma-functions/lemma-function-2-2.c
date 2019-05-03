#include <stddef.h>

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
  requires \valid(in + (0 .. len-1)) ;
  requires l_occurrences_of(v, in, 0, len) > 0 ;
  assigns \nothing ;
  ensures 0 <= \result < len && in[\result] == v ;
*/
size_t occ_not_zero_some_is_v(int v, int* in, size_t len){
  /*@
    loop invariant 0 <= i < len ;
    loop invariant l_occurrences_of(v, in, 0, i) == 0 ;
    loop assigns i ;
    loop variant len-i ;
  */
  for(size_t i = 0 ; i < len ; ++i){
    if(in[i] == v) return i ;
  }
  //@ assert \false ;
  return -1 ;
}

/*@
  requires \valid(in + (0 .. len-1)) ;
  requires l_occurrences_of(v, in, 0, len) > 0 ;
*/
void foo(int v, int* in, size_t len){
  //@ ghost size_t witness = occ_not_zero_some_is_v(v, in, len);
  //@ assert \exists integer n ; 0 <= n < len && in[n] == v ;

  // ... code
}
