#include <limits.h>

/*@ requires b != 0;
    requires a > INT_MIN;
    ensures \result == a % b;
*/
int modulo(int a, int b){
  return a % b ;
}
