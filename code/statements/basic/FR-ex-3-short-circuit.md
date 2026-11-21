Calculons la plus faible précondition pour chaque code, en considérant une
postcondition `Post`.

Avec le court-circuit :

```
wp(if c1 && c2 then c else skip, Post) =
  (c1 && c2 ==> wp(c, Post)) && (! (c1 && c2) ==> Post)                      (1)
```

Sans le court-circuit :

```
wp(if c1 then (if c2 then c else skip) else skip, Post) =
  (c1 ==> wp(if c2 then c else skip, Post) &&
  (! c1 ==> Post))
=
  (c1 ==> ( (c2 ==> wp(c, Post)) && (!c2 ==> Post) ) && (! c1 ==> Post))     (2)
```

Dans les deux formules, notons `X := wp(c, Post)` :

```
(1):  (c1 && c2 ==> X) && (! (c1 && c2) ==> Post)
(2):  (c1 ==> ( (c2 ==> X) && (!c2 ==> Post) ) && (! c1 ==> Post))
```

Simplifions les deux formules.

```
(1)
      (c1 && c2 ==> X) && (! (c1 && c2) ==> Post)
<==>  ( !(c1 && c2) || X ) && ( (c1 && c2) || Post )

<==>  ( !c1 || !c2 || X ) && ( (c1 && c2) || Post )
```

```
(2)
      (c1 ==> ( (c2 ==> X) && (!c2 ==> Post) ) && (! c1 ==> Post))
<==>  ( !c1 || ( (c2 ==> X) && (!c2 ==> Post) ) && (c1 || Post))
<==>  ( !c1 || ( (!c2 || X) && (c2 || Post) ) && (c1 || Post))
<==>  ( !c1 || ( (!c2 || X) && (c2 || Post) ) && (c1 || Post)
<==>  (!c1 || !c2 || X ) && ( (!c1 || c2) || Post) ) && (c1 || Post)
<==>  ( !c1 || !c2 || X ) && ( ((!c1 || c2) && c1) || Post )

<==>  ( !c1 || !c2 || X ) && ( (c2 && c1) || Post )
```

Les deux préconditions générées sont équivalentes.
