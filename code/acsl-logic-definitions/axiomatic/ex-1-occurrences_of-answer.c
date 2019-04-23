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
        (from < to && in[from] == v) ==>
      l_occurrences_of(v,in,from,to) == 1+l_occurrences_of(v,in,from+1,to);

    axiom occurrences_positive_range_without_element{L}:
      \forall int v, int* in, integer from, to;
        (from < to && in[from] != v) ==>
      l_occurrences_of(v,in,from,to) == l_occurrences_of(v,in,from+1,to);
  }
*/

/*@
  requires \valid_read(in+(0 .. length));
  assigns  \nothing;
  ensures  \result == l_occurrences_of(value, in, 0, length);
*/
size_t occurrences_of(int value, int* in, size_t length){
  size_t result = 0;
  
  /*@
    loop invariant 0 <= i <= length;
    loop invariant 0 <= result <= length - i ;
    loop invariant result == l_occurrences_of(value, in, i, length);
    loop assigns i, result;
    loop variant i;
  */
  for(size_t i = length; i > 0 ; --i)
    result += (in[i-1] == value)? 1 : 0;

  return result;
}
