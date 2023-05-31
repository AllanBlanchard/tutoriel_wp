#include <limits.h>

/*@ requires x > INT_MIN ;
    terminates \true ;
*/
int abs(int x){
  return (x < 0) ? -x : x ;
}
