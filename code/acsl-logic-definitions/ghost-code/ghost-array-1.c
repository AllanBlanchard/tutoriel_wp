void function(int a[5]){
  //@ ghost int even[5] = { 0 };

  for(int i = 0; i < 5; ++i){
    //@ ghost if(a[i] % 2) even[i] = 1;
  }
}
