#include <stdlib.h>

/*@ exits \exit_status == 1 ;
    ensures \false ;
*/
void this_function_exits(void){
  exit(1);
}
