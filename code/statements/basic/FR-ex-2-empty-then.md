## Branche "then" vide

En remplaçant dans la règle d'inférence :

```
{ P && cond } skip { Q }        { P && !cond } c { Q }
------------------------------------------------------
        { P } if cond then skip else c { Q }
```

nous voyons que `P && cond` doit impliquer `Q`. En utilisant la
règle de conséquence sur la branche `then` et en rappelant que la
règle du `skip` est `{ P } skip { P }`, nous pouvons écrire :

```
{ P && cond ==> Q }      { Q } skip { Q }
-----------------------------------------
       { P && cond } skip { Q }            { P && !cond } c { Q }
       ----------------------------------------------------------
                 { P } if cond then skip else c { Q }
```


## Branches vides

En remplaçant dans la règle d'inférence :

```
{ P && cond } skip { Q }        { P && !cond } skip { Q }
---------------------------------------------------------
        { P } if cond then skip else skip { Q }
```

A la fois `P && cond` et `P && !cond` doivent impliquer `Q`, donc,
peut importe la valeur de `cond`, `P` doit impliquer `Q`. Nous pouvons
donc écrire, via la règle de conséquence :

```
             { Q && cond } skip { Q }        { Q && !cond } skip { Q }
             ---------------------------------------------------------
  { P ==> Q }         { Q } if cond then skip else skip { Q }
-------------------------------------------------------------
	{ P } if cond then skip else skip { Q }
```

Qui est un arbre de dérivation valide puisque dans les deux branches de la
conditionnelle, en utilisant à nouveau la règle de conséquence, peu importe
que `B` soit `cond` ou `!cond`, nous pouvons écrire :

```
{ Q && cond ==> Q }          { Q } skip { Q }
---------------------------------------------
         { Q && cond } skip { Q }
```

Par conséquent, puisque dans le précédent arbre de dérivation, nous avons le
triplet :

```
{ Q } if cond then skip else skip { Q }
```

Nous pouvons conclure que cette structure dans son ensemble est équivalente
à une instruction `skip`.
