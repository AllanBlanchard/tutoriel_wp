#ifndef _MAX
#define _MAX

#include "max.h"

/*@
  ensures \result >= a && \result >= b;
  ensures \result == a || \result == b;
  assigns \nothing ;
*/
int max(int a, int b);

#endif
