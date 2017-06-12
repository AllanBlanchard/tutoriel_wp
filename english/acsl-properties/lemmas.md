Lemmas are general properties about predicates or functions. Once these
properties are expressed, their proof can be performed (one time) and the
provers will then be able to use this result to perform other proofs without
requiring to perform again all steps needed to perform the original proof if
it appears in a much longer proof about an other property.

For example, lemmas allow us to express properties about recursive functions
in order to get easier proofs when we are interested in proving properties
that use such functions.

# Syntax

Again, we introduce lemmas using ACSL annotations. The syntax is following:

```c
/*@
  lemma name_of_the_lemma { Label0, ..., LabelN }:
    property ;
*/
```

This time, the properties we want to express to depend on recieved parameters
(except for labels). So we will express these properties on universally
quantified variables. For example, we can state this lemma, which is true,
even if it is trivial:


```c
/*@
  lemma lt_plus_lt:
    \forall integer i, j ; i < j ==> i+1 < j+1;
*/
```

This proof can be performed using WP. The property is, of course, proved
using only Qed.

# Exampel : properties about affine functions

We can come back to our affine functions and express some interesting
properties about them:

```c
/* @
  lemma ax_b_monotonic_neg:
    \forall integer a, b, i, j ;
      a <  0 ==> i <= j ==> ax_b(a, i, b) >= ax_b(a, j, b);
  lemma ax_b_monotonic_pos:
    \forall integer a, b, i, j ;
      a >  0 ==> i <= j ==> ax_b(a, i, b) <= ax_b(a, j, b);
  lemma ax_b_monotonic_nul:
    \forall integer a, b, i, j ;
      a == 0 ==> ax_b(a, i, b) == ax_b(a, j, b);
*/
```

For these proofs, Alt-ergo, will probably not be able to discharge generated
goals. In this case, Z3 will certainly perform it. We can then write some
code examples:

```c
/*@
  requires a > 0;
  requires limit_int_min_ax_b(a,4) < x < limit_int_max_ax_b(a,4);
  assigns \nothing ;
  ensures \result == ax_b(a,x,4);
*/
int function(int a, int x){
  return a*x + 4;
}

/*@ 
  requires a > 0;
  requires limit_int_min_ax_b(a,4) < x < limit_int_max_ax_b(a,4) ;
  requires limit_int_min_ax_b(a,4) < y < limit_int_max_ax_b(a,4) ;
  assigns \nothing ;
*/
void foo(int a, int x, int y){
  int fmin, fmax;
  if(x < y){
    fmin = function(a,x);
    fmax = function(a,y);
  } else {
    fmin = function(a,y);
    fmax = function(a,x);
  }
  //@assert fmin <= fmax;
}
```

If we do not give the lemmas provided ealier, Alt-ergo will not be able to prove
the proof that `fmin` is lesser or equal to `fmax`. With the lemmas it is however
very easy for it since the property is the simply an instance of the lemma
`ax_monotonic_pos`, the proof is then trivial as our lemme is considered to be
true when are not currently proving it.