/* run.config
   STDOPT:
   STDOPT:+"-lib-entry"
   STDOPT:+"-main f"
*/

int h = 42 ;

//@ requires 0 <= h <= 100 ;
int main(void){
  //@ assert h == 42 ;
}

//@ requires 0 <= h <= 100 ;
void f(void){
  //@ assert h == 42 ;
}
