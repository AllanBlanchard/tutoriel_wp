struct stack_int{
  size_t top;
  int    data[MAX_SIZE];
};

/*@
  predicate valid_stack_int(struct stack_int* s) = // à définir ;
  predicate empty_stack_int(struct stack_int* s) = // à définir ;
  predicate full_stack_int(struct stack_int* s) =  // à définir ;
*/

/*@
  requires \valid(s);
  assigns *s;
  ensures valid_stack_int(s) && empty_stack_int(s);
*/
void initialize(struct stack_int* s);

/*@
  requires valid_stack_int(s) && !full_stack_int(s);
  assigns  *s;
  ensures valid_stack_int(s);
*/
void push(struct stack_int* s, int value);

/*@
  requires valid_stack_int(s) && !empty_stack_int(s);
  assigns \nothing;
*/
int  top(struct stack_int* s);

/*@
  requires valid_stack_int(s) && !empty_stack_int(s);
  assigns *s;
  ensures valid_stack_int(s);
*/
void pop(struct stack_int* s);

/*@
  requires valid_stack_int(s);
  assigns \nothing;
  ensures \result == 1 <==> empty_stack_int(s);
*/
int  is_empty(stack_int_t s);


/*@
  requires valid_stack_int(s);
  assigns \nothing;
  ensures \result == 1 <==> full_stack_int(s);
*/
int  is_full(stack_int_t s);
