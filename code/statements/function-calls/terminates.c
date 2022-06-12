/* run.config
   STDOPT:+"-wp-no-rte"
   STDOPT:+"-wp-no-rte -wp-variant-with-terminates"
*/

//@ terminates \false ;
void may_not_terminate(void){

}

void call(int r);

//@ terminates r > 0 ;
void simple(int r){
  r -- ;
  call(r);
}

//@ terminates r > 0 ;
void cond_may_not_terminate(int r){
  if(r <= 0){ // if we enter here, r > 0 is false at Pre
    // here statements are not force to terminate: FALSE ==> P is always true
    while(1){}
  }
}

//@ terminates value > 0 ;
void callee(int value);

//@ terminates p > 0 ;
void with_calls(int p){
  // goal: p > 0 ==> p+1 > 0 ; (provable)
  callee(p+1);
  // goal: p > 0 ==> p-1 > 0 ; (not provable, the function may not terminate)
  callee(p-1);
}

//@ terminates value > 0 ;
void with_loop(int value){
  if(value <= 0){
    //@ loop assigns \nothing ;
    while(1){
      // code
    }
  }
}

//@ terminates n > 0 ;
void missing_decreases(int n){
  missing_decreases(n);
}

/*@ requires n >= -1 ;
    terminates n >= 0 ;
    decreases n ; // is verified only with option -wp-variant-with-terminates
*/
void recursive(int n){
  if(n == -1) recursive(n) ;
  else if(n > 0) recursive(n - 1);
}
