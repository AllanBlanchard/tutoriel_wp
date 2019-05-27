/*@ 
  requires \valid_read(a);
  requires *a <= INT_MAX - 5 ;

  assigns \nothing ;

  ensures \result == *a + 5 ; 
*/
int plus_5(int* a){
  return *a + 5 ;
}
