/* run.config
  DONTRUN:
*/

int x ;
int y ;

// 8.
/*@ requires P(x) ;
    ensures P(x) ;
    ensures P(y) ;
*/
void toy(void){
  // 7.
  if(x > 0){
    // 6.
    x ++ ;
    // 5.
    //@ assert Q(x);
  } else {
    // 4.
    y ++ ;
    // 3.
    //@ check Q(y);
  }
  // 2.
  x = x * y ;
  // 1.
}
