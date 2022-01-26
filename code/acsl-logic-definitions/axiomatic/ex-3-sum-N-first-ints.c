/* run.config
   OPT:
*/

#include <limits.h>

/*@ axiomatic Sum_n {
      // ...
    }
*/

/*@ lemma sum_n_value: \true; // to complete */

/*@
  requires n >= 0 ;
  // requires ...
  // assigns ...
  // ensures ...
*/
int sum_n(int n){
  if(n < 1) return 0 ;

  int res = 0 ;
  /*@ loop invariant 1 <= i <= n+1 ;
      // ...
  */
  for(int i = 1 ; i <= n ; i++){
    res += i ;
  }
  return res ;
}
