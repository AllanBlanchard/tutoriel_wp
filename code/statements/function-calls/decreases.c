/*@ requires n >= 0 ;
    decreases n ;
*/
void ends(int n){
  if(n > 0) ends(n-1);
}
