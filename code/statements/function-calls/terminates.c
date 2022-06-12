



//@ terminates \false ;
void may_not_terminate(void){

}

//@ terminates r > 0 ;
void simple(int r){
  r -- ;
  call();
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
