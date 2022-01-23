/* run.config
   DONTRUN:
*/

void max_ptr(int* a, int* b){
  if(*a < *b){
    int tmp = *b ;
    *b = *a ;
    *a = tmp ;
  }
}

void min_ptr(int* a, int* b){
  max_ptr(b, a);
}

void order_3_inc_min(int* a, int* b, int* c){
  min_ptr(a, b) ;
  min_ptr(a, c) ;
  min_ptr(b, c) ;
}

void incr_a_by_b(int* a, int const* b){
  *a += *b;
}
