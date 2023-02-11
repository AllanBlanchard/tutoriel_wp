/* run.config
   DEPS: abs.h max.h max_abs.h
   STDOPT:
*/

#include <limits.h>
#include "max_abs.h"
#include "abs.h"
#include "max.h"

int max_abs(int a, int b){
  int abs_a = abs(a);
  int abs_b = abs(b);

  return max(abs_a, abs_b);
}
