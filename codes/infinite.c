void foo(){
  while(1){}
  //@ assert \false;
}

void bar(){
  goto End;
  //@ assert \false;
 End:
}
