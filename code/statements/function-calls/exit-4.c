#include <stdlib.h>

/*@ behavior exits:
      assumes x == 0; 
      exits \exit_status == 1 ;
      ensures \false ;
    behavior is_ok:
      assumes x != 0 ;
      exits \false ;
*/
void this_function_exits(int x){
  if(!x) exit(1);
}

void does_this_function_exit(void){
  this_function_exits(1);
}
