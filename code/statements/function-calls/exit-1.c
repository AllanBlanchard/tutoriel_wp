#include <stdlib.h>

/*@ exits \true ;
    ensures \false ;
*/
void this_function_exits(void){
  exit(1);
}
