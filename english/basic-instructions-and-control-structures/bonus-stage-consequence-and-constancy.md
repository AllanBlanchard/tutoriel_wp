# Règle de conséquence

Parfois, il peut être utile pour la preuve de renforcer une post-condition ou 
d'affaiblir une pré-condition. Si la première sera souvent établie par nos soins
pour faciliter le travail du prouveur, la seconde est plus souvent vérifiée 
par l'outil à l'issu du calcul de plus faible pré-condition.

La règle d'inférence en logique de Hoare est la suivante :

->$\dfrac{P \Rightarrow WP \quad \{WP\}\quad c\quad \{SQ\} \quad SQ \Rightarrow Q}{\{P\}\quad c \quad \{Q\}}$<-

(Nous noterons que les prémisses, ici, ne sont pas seulement des triplets de
Hoare mais également des formules à vérifier)

Par exemple, si notre post-condition est trop complexe, elle risque de générer
une plus faible pré-condition trop compliquée et de rendre le calcul des 
prouveurs difficile. Nous pouvons alors créer une post-condition intermédiaire
$SQ$, plus simple, mais plus restreinte et impliquant la vraie post-condition. 
C'est la partie $SQ \Rightarrow Q$.

Inversement, le calcul de pré-condition générera généralement une formule 
compliquée et souvent plus faible que la pré-condition que nous souhaitons
accepter en entrée. Dans ce cas, c'est notre outil qui s'occupera de vérifier 
l'implication entre ce que nous voulons et ce qui est nécessaire pour que notre
code soit valide. C'est la partie $P \Rightarrow WP$.

Nous pouvons par exemple illustrer cela avec le code qui suit. Notons bien qu'ici,
le code pourrait tout à fait être prouvé par l'intermédiaire de WP sans ajouter des
affaiblissements et renforcements de propriétés car le code est très simple, il 
s'agit juste d'illustrer la règle de conséquences.

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

(À noter ici : nous avons omis les contrôles de débordement d'entiers).

Ici, nous voulons avoir un résultat compris entre 0 et 100. Mais nous savons que
le code ne produira pas un résultat sortant des bornes 10 à 90. Donc nous 
renforçons la post-condition avec une assertion que `res`, le résultat, est compris
entre 0 et 90 à la fin. Le calcul de plus faible pré-condition, sur cette propriété,
et avec l'affectation `res = 10*a` nous produit une plus faible pré-condition 
`1 <= a <= 9` et nous savons finalement que `2 <= a <= 8` nous donne cette garantie.

Quand une preuve a du mal à être réalisée sur un code plus complexe, écrire des
assertions produisant des post-conditions plus fortes mais qui forment des formules
plus simples peut souvent nous aider. Notons que dans le code précédent, les lignes
`P_imply_WP` et `SQ_imply_Q` ne sont jamais utiles car c'est le raisonnement par
défaut produit par WP, elles sont juste présentes pour l'illustration.

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