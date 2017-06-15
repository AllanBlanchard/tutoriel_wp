#include <stdlib.h>

typedef struct cell* list_t;

struct cell{
  int    hd;
  list_t tl;
};

/*@
  axiomatic NotIn{
    predicate not_in(struct cell* c, \list<struct cell*> l) reads l;

    axiom not_in_empty: 
      \forall struct cell* c; not_in(c, \Nil);

    axiom not_in_cons :
      \forall struct cell* c, \list<struct cell*> l, tl ; 
        l == \Cons(c, tl) ==> not_in(c, tl) ==> not_in(c, l);
  }
*/

/*@
  axiomatic C_ListProps{
    logic \list<integer>      values  {L}(list_t l) reads *l;
    logic \list<struct cell*> pointers{L}(list_t l) reads *l;
    predicate no_dup_pointer(\list<struct cell*> l);

    axiom empty_list_nil_values  : values(NULL)   == [| |];
    axiom empty_list_nil_pointers: pointers(NULL) == [| |];

    axiom cons_list_cons_values:
      \forall list_t l; l != NULL ==> 
        values(l)   == \Cons(l->hd, values(l->tl));
    axiom cons_list_cons_pointers:
      \forall list_t l; l != NULL ==> 
        pointers(l) == \Cons(l    , pointers(l->tl));

    axiom no_dup_empty_list: no_dup_pointer(\Nil);
    axiom no_dup_cons:
      \forall \list<struct cell*> l, l2, struct cell* c ; 
        l == \Cons(c, l2) ==>
        not_in(c, l2) && no_dup_pointer(l2) ==> no_dup_pointer(l);
  }
*/

/*@
  predicate wf_list(list_t l) = no_dup_pointer(pointers(l));
*/

/*@
  ensures values(\result) == \Nil;
  ensures wf_list(\result);
*/
list_t initialize(){ return NULL; }

/*@
  requires \valid(c);
  requires wf_list(l);
  requires not_in(c, pointers(l));
  ensures  values(\result) == \Cons(c->hd, values(l));
  ensures  wf_list(\result);
*/
list_t cons(struct cell* c, list_t l){
  //@ assert wf_list(l);
  c->tl = l;
  //@ assert pointers{Here}(l) == pointers{Pre}(l);
  //@ assert wf_list(l);
  //@ assert not_in(c, pointers(l));
  return c;
}
