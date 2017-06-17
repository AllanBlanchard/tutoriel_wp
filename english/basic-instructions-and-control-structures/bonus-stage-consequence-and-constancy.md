# Consequence rule

It can sometimes be useful to strengthen a postcondition or
to weaken a precondition.
If the former will often be established by us to facilitate the work of the
prover, the second is more often verified by the tool as the result of computing
the weakest precondition.

The inference rule of Hoare logic is the following:

->$\dfrac{P \Rightarrow WP \quad \{WP\}\quad c\quad \{SQ\} \quad SQ \Rightarrow Q}{\{P\}\quad c \quad \{Q\}}$<-

(We remark that the premises here are not only Hoare triples but also formulas
to verify.)

For example, if our post-condition is too complex, it may generate a weaker
precondition that is, however, too complicated, thus making the work of provers
more difficult. We can then create a simpler intermediate postcondition $SQ$,
that is, however, stricter and implies the real postcondition.
This is the part $SQ \Rightarrow Q$.

Conversely, the calculation of the precondition will usually generate a
complicated and often weaker formula than the precondition we want to accept as
input. In this case, it is our tool that will check the implication between
what we want and what is necessary for our code to be valid.
Th is is the part $P \Rightarrow WP$.

We can illustrate this with the following code. Note that here the code could
be proved by WP without the weakening and strengthening of properties because
the code is very simple, it is just to illustrate the rule of consequence.


```c
/*@
  requires P: 2 <= a <= 8;
  ensures  Q: 0 <= \result <= 100 ;
  assigns  \nothing ;
*/
int constrained_times_10(int a){
  //@ assert P_imply_WP: 2 <= a <= 8 ==> 1 <= a <= 9 ;
  //@ assert WP:         1 <= a <= 9 ;

  int res = a * 10;

  //@ assert SQ:         10 <= res <= 90 ;
  //@ assert SQ_imply_Q: 10 <= res <= 90 ==> 0 <= res <= 100 ;

  return res;
}
```
(Note: We have omitted here the control of integer overflow.)

Here we want to have a result between 0 and 100. But we know that the code will
not produce a result outside the bounds of 10 and 90. So we strengthen the
postcondition with an assertion that at the end `res`, the result, is between
0 and 90. The calculation of the weakest precondition of this property together
with the assignment `res = 10 * a` yields a weaker precondition `1 <= a <= 9`
and we know that `2 < = a <= 8` gives us the desired guarantee.

When there are difficulties to carry out a proof on more complex code, then it
is often helpful to write assertions that produce stronger, yet easier to
verify, postconditions. Note that in the previous code, the lines `P_imply_WP`
and` SQ_imply_Q` are never used because this is the default reasoning of WP.
They are just here for illustrating the rule.

# Règle de constance

Certaines séquences d'instructions peuvent concerner et faire intervenir des
variables différentes. Ainsi, il peut arriver que nous initialisions et manipulions
un certain nombre de variables, que nous commencions à utiliser certaines d'entre
elles, puis que nous les délaissions au profit d'autres pendant un temps. Quand un
tel cas apparaît, nous avons envie que l'outil ne se préoccupe que des variables
qui sont susceptibles d'être modifiées pour avoir des propriétés les plus légères
possibles.

La règle d'inférence qui définit ce raisonnement est la suivante :

-> $\dfrac{\{P\}\quad c\quad \{Q\}}{\{P \wedge R\}\quad c\quad \{Q \wedge R\}}$ <-

Où $c$ ne modifie aucune variable entrant en jeu dans $R$. Ce qui nous dit : « pour
vérifier le triplet, débarrassons nous des parties de la formule qui concerne des
variables qui ne sont pas manipulées par $c$ et prouvons le nouveau triplet ».
Cependant, il faut prendre garde à ne pas supprimer trop d'informations, au risque
de ne plus pouvoir prouver nos propriétés.

Par exemple, nous pouvons imaginer le code suivant (une nouvelle fois, nous omettons
les contrôles de débordements au niveau des entiers) :

```c
/*@
  requires a > -99 ;
  requires b > 100 ;
  ensures  \result > 0 ;
  assigns  \nothing ;
*/
int foo(int a, int b){
  if(a >= 0){
    a++ ;
  } else {
    a += b ;
  }
  return a ;
}
```

Si nous regardons le code du bloc `if`, il ne fait pas intervenir la variable
`b`, donc nous pouvons omettre complètement les propriétés à propos de  `b` pour
réaliser la preuve que `a` sera bien supérieur à 0 après l'exécution du bloc :

```c
/*@
  requires a > -99 ;
  requires b > 100 ;
  ensures  \result > 0 ;
  assigns  \nothing ;
*/
int foo(int a, int b){
  if(a >= 0){
    //@ assert a >= 0; //et rien à propos de b
    a++ ;
  } else {
    a += b ;
  }
  return a ;
}
```

En revanche, dans le bloc `else`, même si `b` n'est pas modifiée, établir
des propriétés seulement à propos de `a` rendrait notre preuve impossible (en
tant qu'humains). Le code serait :

```c
/*@
  requires a > -99 ;
  requires b > 100 ;
  ensures  \result > 0 ;
  assigns  \nothing ;
*/
int foo(int a, int b){
  if(a >= 0){
    //@ assert a >= 0; // et rien à propos de b
    a++ ;
  } else {
    //@ assert a < 0 && a > -99 ; // et rien à propos de b
    a += b ;
  }
  return a ;
}
```

Dans le bloc `else`, n'ayant que connaissance du fait que `a` est compris
entre -99 et 0, et ne sachant rien à propos de `b`, nous pourrions
difficilement savoir si le calcul `a += b` produit une valeur supérieure
strict à 0 pour `a`.

Naturellement ici, WP prouvera la fonction sans problème, puisqu'il transporte
de lui-même les propriétés qui lui sont nécessaires pour la preuve. En fait,
l'analyse des variables qui sont nécessaires ou non (et l'application, par
conséquent de la règle de constance) est réalisée directement par WP.

Notons finalement que la règle de constance est une instance de la règle de
conséquence :

->$\dfrac{P \wedge R \Rightarrow P \quad \{P\}\quad c\quad \{Q\} \quad Q \Rightarrow Q \wedge R}{\{P \wedge R\}\quad c\quad \{Q \wedge R\}}$ <-

Si les variables de $R$ n'ont pas été modifiées par l'opération (qui par contre,
modifie les variables de $P$ pour former $Q$), alors effectivement
$P \wedge R \Rightarrow P$ et $Q \Rightarrow Q \wedge R$.
