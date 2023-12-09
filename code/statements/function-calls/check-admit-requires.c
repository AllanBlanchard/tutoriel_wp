/* run.config
   STDOPT: +"-wp-no-rte"
*/

/*@       requires R1: *x >= 0 ;
    check requires R2: *y >= 10 ;
    admit requires R3: *z >= 30 ;
    assigns *x, *y, *z ;
*/
void callee(int *x, int *y, int *z){
  //@ check A1: *x >= 0 ;
  //@ check A2: *y >= 10 ;
  //@ check A3: *z >= 20 ;
}

void caller(void){
  int x = -1, y = 10, z = 20 ;
  callee(&x, &y, &z);

  //@ check \false ;
}
