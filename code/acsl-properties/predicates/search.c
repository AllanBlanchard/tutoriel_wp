/* run.config
   DONTRUN:
*/

#include <stddef.h>

/*@
  predicate valid_range_rw(int* t, integer n) =
    n >= 0 && \valid(t + (0 .. n-1));

  predicate valid_range_r(int* t, integer n) =
    n >= 0 && \valid_read(t + (0 .. n-1));
*/

/*@
  requires 0 < length;
  requires valid_range_r(array, length);
  //...
*/
int* search(int* array, size_t length, int element);
