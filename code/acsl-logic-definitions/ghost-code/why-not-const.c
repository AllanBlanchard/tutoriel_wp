/* run.config
   EXIT: 1
   STDOPT:
*/

/*@ ghost
  /@ assigns *p ;
     ensures *p == \old(*q); @/
  void assign(int * \ghost * p, int * \ghost * q){
    *p = *q ;
  }
*/
void caller(void){
  int x ;

  //@ ghost int \ghost * p ;
  //@ ghost int * q = &x ;
  //@ ghost assign(&p, &q) ;
  //@ ghost *p = 42 ;
}
