#include <stddef.h>

/*@
  predicate valid_range_ro(int* t, integer beg, integer end) =
    end >= beg && \valid_read(t + (beg .. end-1)) ;

  predicate valid_range_ro(int* t, integer n) =
    valid_range_ro(t, 0, n) ;
*/

/*@
  requires 0 < length;
  requires valid_range_ro(array, length);
  //...
*/
int* search(int* array, size_t length, int element);
