/* run.config
   DONTRUN:
*/

int alphabet_letter(char c){
  if( ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') ) return 1 ;
  else return 0 ;
}

int main(){
  int r ;

  r = alphabet_letter('x') ;
  //@ assert r ;
  r = alphabet_letter('H') ;
  //@ assert r ;
  r = alphabet_letter(' ') ;
  //@ assert !r ;
}
