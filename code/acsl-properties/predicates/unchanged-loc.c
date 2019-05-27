/*@
  predicate unchanged{L0, L1}(int* i) =
    \at(*i, L0) == \at(*i, L1);
*/

int main(void){
  int i = 13;
  int j = 37;

 Begin:
  i = 23;
 
  //@assert ! unchanged{Begin, Here}(&i);
  //@assert   unchanged{Begin, Here}(&j);
}
