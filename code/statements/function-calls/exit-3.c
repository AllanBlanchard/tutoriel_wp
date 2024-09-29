#include <stdlib.h>

/*@ exits \exit_status == 1 ;
    ensures \false ;
*/
void this_function_exits(void){
  exit(1);
}

void does_this_function_exit(void){
  this_function_exits();
}
