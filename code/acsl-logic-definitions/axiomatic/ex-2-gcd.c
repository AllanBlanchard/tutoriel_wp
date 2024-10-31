/* run.config
   OPT:
*/

#include <limits.h>

/*@
  axiomatic GCD {
    // ...
  }
*/

/*@
  requires a >= 0 && b >= 0 ;
  // assigns ...
  // ensures ...
*/
int gcd(int a, int b){
  while (b != 0){
    int t = b;
    b = a % b;
    a = t;
  }
  return a;
}
