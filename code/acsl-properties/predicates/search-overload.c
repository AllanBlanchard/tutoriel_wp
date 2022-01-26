/* run.config
   OPT:
*/

#include <stddef.h>

/*@
  predicate valid_range_r(int* t, integer beg, integer end) =
    end >= beg && \valid_read(t + (beg .. end-1)) ;

  predicate valid_range_r(int* t, integer n) =
    valid_range_r(t, 0, n) ;
*/

/*@
  requires 0 < length;
  requires valid_range_r(array, length);
  //...
*/
int* search(int* array, size_t length, int element);
