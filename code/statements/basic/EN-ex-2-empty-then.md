## Empty "then" branch

By replacing in the inference rule:

```
{ P && cond } skip { Q }        { P && !cond } c { Q }
------------------------------------------------------
        { P } if cond then skip else c { Q }
```

we see that `P && cond` must imply `Q`. By using the consequence
rule on the `then` branch, considering that the rule of `skip` is
`{ P } skip { P }`, we can write:

```
{ P && cond ==> Q }      { Q } skip { Q }
-----------------------------------------
       { P && cond } skip { Q }            { P && !cond } c { Q }
       ----------------------------------------------------------
                 { P } if cond then skip else c { Q }
```


## Empty branches

By replacing in the inference rule:

```
{ P && cond } skip { Q }        { P && !cond } skip { Q }
---------------------------------------------------------
        { P } if cond then skip else skip { Q }
```

Both `P && cond` and `P && !cond` must imply `Q`, thus, no
matter what `cond`, `P` must imply `Q`. Thus we could have
written using the consequence rule:


```
             { Q && cond } skip { Q }        { Q && !cond } skip { Q }
             ---------------------------------------------------------
  { P ==> Q }         { Q } if cond then skip else skip { Q }
-------------------------------------------------------------
	{ P } if cond then skip else skip { Q }
```


Which is a valid derivation tree because in both branches of the conditional,
by using again the consequence rule, no matter if `B` is `cond` or `!cond`, we
can write:

```
{ Q && cond ==> Q }          { Q } skip { Q }
---------------------------------------------
         { Q && cond } skip { Q }
```

Thus, since in the previous derivation tree we have the triple:

```
{ Q } if cond then skip else skip { Q }
```

We can conclude that the complete statement is equivalent to a `skip` acion.