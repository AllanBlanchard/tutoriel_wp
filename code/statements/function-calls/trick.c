/*@
  assigns \nothing ;
  ensures \false ;
*/
void trick(){
  trick() ;
}

int main(){
  trick();
  //@ assert \false ;
}
