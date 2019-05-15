int main(){
  int a = 42;
 Label_a:
  a = 45;
  
  //@assert a == 45 && \at(a, Label_a) == 42;
}
