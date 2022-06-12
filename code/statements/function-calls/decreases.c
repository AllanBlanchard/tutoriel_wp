/*@ requires n >= 0 ;
    decreases n ;
*/
void ends(int n){
  if(n > 0) ends(n-1);
}

/*@ requires n >= 0 ;
    decreases n ;
*/
void ends_2(int n){
  if(n > 0) ends_2(n-1); // Ok: 0 <= n-1 < n
  if(n > 0) ends_2(n-1); // Ok: 0 <= n-1 < n, no need to be less than call on l.5
}

/*@ requires *p >= 0 ;
    decreases *p ;
*/
void ends_ptr(int *p){
  if(*p > 0){
    (*p)-- ;
    ends_ptr(p); // Ok: 0 <= *p < \at(*p, Pre)
  }
}

//@ decreases v ;
void single(unsigned v){
  if(v > 0) single(v-1); // OK: 0 <= v-1 < v
}

//@ decreases k-1 ;
void mutual_2(unsigned k);

//@ decreases n ;
void mutual_1(unsigned n){
  if(n > 1) mutual_2(n-1); // OK: 0 <= (n-1)-1 < n
}

void mutual_2(unsigned k){
  if(k > 1) mutual_1(k-2); // OK: 0 <= (k-2) < k-1
  single(k+1) ; // no verification needed, s in not in the cluster
}
