/* run.config
   DEPS: abs.h
   STDOPT:
*/

#include "abs.h"

int abs(int val){
  if(val < 0) return -val;
  return val;
}
