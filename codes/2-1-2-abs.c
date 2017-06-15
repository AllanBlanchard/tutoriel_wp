#include <limits.h>

/*@
  requires val > INT_MIN ;

  ensures positive_value: function_result: \result >= 0;
  ensures (val >= 0 ==> \result == val) && 
          (val < 0 ==> \result == -val);
*/
int abs(int val){
  if(val < 0) return -val;
  return val;
}
