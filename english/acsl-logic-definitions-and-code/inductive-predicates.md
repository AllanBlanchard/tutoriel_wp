Inductive predicates gives a way to state properties whose verification requires
to reason by induction, that is to say: for a property $p(input)$, it is true
for some base cases (for example, $0$ is an even natural number), and knowing
that $p(input)$ is true, it also true for a $bigger input$, provided some
conditions relating $input$ and $bigger input$ (for example, knowing that $n$ is
even, we define that $n+2$ is also even). Thus, inductive predicates are
generally useful to define properties recursively.

# Syntax

For now, let us define the syntax of inductive predicates:

```c
/*@
  inductive property{ Label0, ..., LabelN }(type0 a0, ..., typeN aN) {
  case c_1{L0, ..., Lq}: p_1 ;
  ...
  case c_m{L0, ..., Lr}: p_km ;
  }
*/
```

Where all `c_i` are names and all `p_i` are logic formulas where
`property` appears has a conclusion. Basically, `property` is true for
some parameters and some labels, if it corresponds to one of the cases
of the inductive definition.

We can have a look to the simple property we just talked about: how to define
that a natural number is even using induction. We can translate the sentence:
"0 is a natural number, and if $n$ is a natural number, $n+2$ is a natural
number":

```c
/*@
  inductive even_natural{L}(integer n) {
  case even_nul{L}:
    even_natural(0);
  case even_not_nul_natural{L}:
    \forall integer n ; 
      even_natural(n) ==> even_natural(n+2);
  }
*/
```

Which perfectly describes the two cases:

- $0$ is even (base case),
- if a natural $n$ is even, $n+2$ is also even.

However, this definition is not completely satisfaying. For example, we cannot
deduce that an odd number is not even. If we try to prove that 1 is even, we
will have to check if -1 is even, and then -3, -5, etc, infinitely. Moreover,
we generally prefer to define the induction cases the opposite way: defining
the condition under which the wanted conclusion is true. For example, here,
how can we verify that some $n$ is natural and even? We first have to check that
$n$ is greater than $0$ and then to verify that $n-2$ is even:

```c
/*@
  inductive even_natural{L}(integer n) {
  case even_nul{L}:
    even_natural(0) ;
  case even_not_nul_natural{L}:
    \forall integer n ; n > 0 ==> even_natural(n-2) ==>
      even_natural(n) ;
  }
*/
```

Here, we distinguish two cases:

- 0 is even,
- a natural $n$ is even if $n-2$ is an even natural.

Taking the second case, we recursively decrease the number until we reach
0 - and then the number is even, since 0 is even - or -1, and then there
is no case in the inductive that corresponds to this value, so we could
deduce that the property is false (however, SMT solvers are generally not
could at reasoning by induction, but we will see how to ease this later).

[INSERT EXAMPLE OF PROOF]

Of course, defining that some natural number is even inductively is not a
good idea, since we can simply define it using modulo. We generally use them
to define complex recursive properties.

