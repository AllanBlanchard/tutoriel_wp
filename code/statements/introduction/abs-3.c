int abs(int val){
  int res;
  if(val < 0){
    //@ assert val < 0 ;
    res = - val;
    //@ assert \at(val, Pre) >= 0 ==> res == val && \at(val, Pre) < 0 ==> res == -val ;
  } else {
    //@ assert !(val < 0) ;
    res = val;
    //@ assert \at(val, Pre) >= 0 ==> res == val && \at(val, Pre) < 0 ==> res == -val ;
  }
  //@ assert \at(val, Pre) >= 0 ==> res == val && \at(val, Pre) < 0 ==> res == -val ;

  return res;
}
