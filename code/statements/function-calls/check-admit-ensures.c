/* run.config
   STDOPT: +"-wp-no-rte"
*/

/*@ assigns *x, *y, *z ;
          ensures E1: *x >= 0 ;
    check ensures E2: *y >= 10 ;
    admit ensures E3: *z >= 30 ;
*/
void callee(int *x, int *y, int *z){
  *x = -1 ;
  *y = 10 ;
  *z = 20 ;
}

void caller(void){
  int x, y, z ;
  callee(&x, &y, &z);

  //@ check A1: x >= 0;
  //@ check A2: y >= 10 ;
  //@ check A3: z >= 30 ;
}
