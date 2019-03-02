void max_ptr(int* a, int* b){
  if(*a < *b){
    int tmp = *b ;
    *b = *a ;
    *a = tmp ;
  }
}

void min_ptr(int* a, int* b){
  // use max_ptr
}

void order_3_inc_max(int* a, int* b, int* c){
  //in increasing order using max_ptr
}

void order_3_inc_min(int* a, int* b, int* c){
  //in increasing order using min_ptr
}

void order_3_dec_max(int* a, int* b, int* c){
  //in decreasing order using max_ptr
}

void order_3_dec_min(int* a, int* b, int* c){
  //in decreasing order using min_ptr
}
