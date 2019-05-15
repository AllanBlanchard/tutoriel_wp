#ifndef _ABS
#define _ABS

#include <limits.h>

/*@
  requires val > INT_MIN;
  assigns  \nothing;

  behavior pos:
    assumes 0 <= val;
    ensures \result == val;
  
  behavior neg:
    assumes val < 0;
    ensures \result == -val;
 
  complete behaviors;
  disjoint behaviors;
*/
int abs(int val);

#endif
