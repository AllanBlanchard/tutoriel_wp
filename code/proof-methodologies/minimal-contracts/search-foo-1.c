void foo(int* array, size_t length){
  int* p = search(array, length, 0) ;
  if(p){
    *p += 1 ;
  }
}
