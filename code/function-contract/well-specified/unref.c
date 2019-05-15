/*@ requires \valid(p); */
int unref(int* p){
  return *p;
}

int const value = 42;

int main(){
  int i = unref(&value);
}
