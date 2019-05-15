#include <stddef.h>

/*@
  ensures min <= \result <= max;
*/
size_t random_between(size_t min, size_t max);

void undetermined_loop(size_t bound){
  /*@
    loop invariant 0 <= i <= bound ;
    loop assigns i;
    loop variant i;
   */
  for(size_t i = bound; i > 0; ){
    i -= random_between(1, i);
  }
}
