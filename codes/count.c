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
        (from < to+1 && in[to] == v) ==>
      l_occurrences_of(v,in,from,to+1) == 1+l_occurrences_of(v,in,from,to);

    axiom occurrences_positive_range_without_element{L}:
      \forall int v, int* in, integer from, to;
        (from < to+1 && in[to] != v) ==>
      l_occurrences_of(v,in,from,to+1) == l_occurrences_of(v,in,from,to);
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
    loop invariant 0 <= result <= i <= length;
    loop invariant result == l_occurrences_of(value, in, 0, i);
    loop assigns i, result;
    loop variant length-i;
  */
  for(size_t i = 0; i < length; ++i)
    result += (in[i] == value)? 1 : 0;

  return result;
}
