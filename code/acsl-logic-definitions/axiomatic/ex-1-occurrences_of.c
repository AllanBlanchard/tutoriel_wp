/* run.config
   OPT:
*/

#include <stddef.h>

/*@
  axiomatic Occurrences_Axiomatic{
    logic integer l_occurrences_of{L}(int value, int* in, integer from, integer to)
      reads in[from .. to-1];

    axiom occurrences_empty_range{L}: \true; // to complete
    axiom occurrences_positive_range_with_element{L}: \true; // to complete
    axiom occurrences_positive_range_without_element{L}: \true; // to complete
  }
*/

/*@
  requires \valid_read(in+(0 .. length));
  assigns  \nothing;
  ensures  \result == l_occurrences_of(value, in, 0, length);
*/
size_t occurrences_of(int value, int* in, size_t length){
  size_t result = 0;

  for(size_t i = length; i > 0 ; --i)
    result += (in[i-1] == value) ? 1 : 0;

  return result;
}
