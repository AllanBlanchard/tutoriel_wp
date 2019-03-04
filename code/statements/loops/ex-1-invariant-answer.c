void foo(){
  int x = 0 ;

  /*@ loop invariant -10 <= x <= 0 ; */
  while(x > -10){
    -- x ;
  }
}

/*
  -100 <= x <= 100 is a correct loop invariant.
  
  ----  ESTABLISHMENT
  -100 <= 0 <= 100 is verified

  ----  PRESERVATION
  For any iteration, we have -100 <= x <= 100.
  
  -  If x <= -10, we leave the loop and the invariant is verified
  -  If x >  -10, we have -10 < x <= 100.
     After the block of the loop, we have: -10 <= x < 100 which implies -100 <= x <= 100.
*/

void bar(){
  int x = 0 ;

  /*@ loop invariant -100 <= x <= 100 ; */
  while(x > -10){
    -- x ;
  }
}
