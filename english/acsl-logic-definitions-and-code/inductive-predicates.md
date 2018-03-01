Inductive predicates are generally useful to define properties
recursively. For now, let us define the syntax of inductive predicates:

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

We can have a look to a first simple property: how to define that a
natural number is even only using the `-` operator. We can write:

```c
/*@
  inductive even_natural{L}(integer n) {
  case even_nul{L}:
    even(0) ;
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
deduce that the property is false.

