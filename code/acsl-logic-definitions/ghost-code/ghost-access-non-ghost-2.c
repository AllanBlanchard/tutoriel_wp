/* run.config
   EXIT: 1
   STDOPT:
*/

#include <limits.h>

int sum(int n){
  int x = 0 ;
  for(int i = 0; i <= n; ++i){
    x += i ;
    /*@ ghost
      if (x < INT_MAX){
        x++;
        x--; // assure that x remains coherent
      }
    */
  }
  return x;
}
