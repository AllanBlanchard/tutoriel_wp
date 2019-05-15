#include <stdlib.h>

#define MAX 64

struct stack{
  int    array[MAX];
  size_t top;
};

/*@
  axiomatic StackSpec{
    logic \list<integer> represents(struct stack* s) reads *s;

    axiom empty: 
      \forall struct stack* s ; s->top == 0 ==> represents(s) == \Nil;
  }
*/


/*@
  requires s != NULL;
  assigns  s->top;
  ensures  represents(s) == \Nil;
*/
void initialize(struct stack* s){
  s->top = 0;
}

void push(struct stack* s, int data){
  s->array[s->top++] = data;
}

int top(struct stack* s){
  return s->array[s->top];
}

void pop(struct stack* s){
  s->top--;
}
