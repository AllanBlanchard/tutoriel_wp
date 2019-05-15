Let us first compute the weakest precondition of each source code, considering
a postcondition `Post`.

Without short circuit:

```
wp(if c1 && c2 then c else skip, Post) =
  (c1 && c2 ==> wp(c, Post)) && (! (c1 && c2) ==> Post)                      (1)
```

With short circuit:

```
wp(if c1 then (if c2 then c else skip) else skip, Post) =
  (c1 ==> wp(if c2 then c else skip, Post) &&
  (! c1 ==> Post)
=
  (c1 ==> ( (c2 ==> wp(c, Post)) && (!c2 ==> Post) ) && (! c1 ==> Post)      (2)
```

In both formula, note `X := wp(c, Post)`:

```
(1):  (c1 && c2 ==> X) && (! (c1 && c2) ==> Post)
(2):  (c1 ==> ( (c2 ==> X) && (!c2 ==> Post) ) && (! c1 ==> Post)
```

Let us simplify both formulas.

```
(1)
      (c1 && c2 ==> X) && (! (c1 && c2) ==> Post)
<==>  ( !(c1 && c2) || X ) && ( (c1 && c2) || Post )

<==>  ( !c1 || !c2 || X ) && ( (c1 && c2) || Post )
```

```
(2)
      (c1 ==> ( (c2 ==> X) && (!c2 ==> Post) ) && (! c1 ==> Post)
<==>  ( !c1 || ( (c2 ==> X) && (!c2 ==> Post) ) && (c1 || Post)
<==>  ( !c1 || ( (!c2 || X) && (c2 || Post) ) && (c1 || Post)
<==>  ( !c1 || ( (!c2 || X) && (c2 || Post) ) && (c1 || Post)
<==>  (!c1 || !c2 || X ) && ( (!c1 || c2) || Post) ) && (c1 || Post)
<==>  ( !c1 || !c2 || X ) && ( ((!c1 || c2) && c1) || Post )

<==>  ( !c1 || !c2 || X ) && ( (c2 && c1) || Post )
```

Thus, the generated precondition are equivalent.