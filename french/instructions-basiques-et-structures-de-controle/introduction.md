[[information]]
| Cette partie est plus formelle que ce nous avons vu jusqu'à maintenant. Si le 
| lecteur souhaite se concentrer sur l'utilisation de l'outil, l'introduction de
| ce chapitre et les deux premières sections (sur les instructions de base et « le 
| bonus stage ») sont dispensables. Si ce que nous avons présenté jusqu'à maintenant
| a semblé ardu au lecteur sur un plan formel, il est également possible de réserver 
| l'introduction et ces deux sections pour une deuxième lecture.
| 
| Les sections sur les boucles sont en revanches indispensables. Les éléments plus
| formels de ces sections seront signalés.

Pour chaque notion en programmation C, nous associerons la règle d'inférence qui 
lui correspond, la règle utilisée de calcul de plus faible pré-conditions qui la 
régit, et des exemples d'utilisation. Pas forcément dans cet ordre et avec plus ou 
moins de liaison avec l'outil. Les premiers points seront plus focalisés sur la
théorie que sur l'utilisation car ce sont les plus simples, au fur et à mesure,
nous nous concentrerons de plus en plus sur l'outil, en particulier quand nous 
attaquerons le point concernant les boucles.

# Règle d'inférence

Une règle d'inférence est de la forme :

-> $\dfrac{P_1 \quad ... \quad P_n}{C}$ <-

Et signifie que pour assurer que la conclusion $C$ est vraie, il faut d'abord
savoir que les prémisses $P_1$, ..., et $P_n$ sont vraies. Quand il n'y a
pas de prémisses :

-> $\dfrac{}{\quad C \quad}$ <-

Alors, il n'y a rien à assurer pour conclure que $C$ est vraie.

Inversement, pour prouver qu'une certaine prémisse est vraie, il peut être nécessaire 
d'utiliser une autre règle d'inférence, ce qui nous donnerait quelque
chose comme :

-> $\dfrac{\dfrac{}{\quad P_1\quad} \quad \dfrac{P_{n_1}\quad P_{n_2}}{P_n}}{C}$ <-

Ce qui nous construit progressivement l'arbre de déduction de notre raisonnement.
Dans notre raisonnement, les prémisses et conclusions manipulées seront 
généralement des triplets de Hoare.

# Triplet de Hoare

Revenons sur la notion de triplet de Hoare :

-> $\{ P \}\quad  C\quad \{ Q \}$ <-

Nous l'avons vu en début de tutoriel, ce triplet nous exprime que si avant 
l'exécution de $C$, la propriété $P$ est vraie, et si $C$ termine, alors la
propriété $Q$ est vraie. Par exemple, si nous reprenons notre programme de
calcul de la valeur absolue (légèrement modifié):

```c
/*@
  ensures \result >= 0;
  ensures (val >= 0 ==> \result == val ) && (val <  0 ==> \result == -val);
*/
int abs(int val){
  int res;
  if(val < 0) res = - val;
  else        res = val;

  return res;
}
```

Ce que nous dit Hoare, est que pour prouver notre programme, les propriétés
entre accolades dans ce programme doivent être vérifiées (j'ai omis une des
deux post-conditions pour alléger la lecture) :

```c
int abs(int val){
  int res;
// { P }
  if(val < 0){
// {  (val < 0) && P }
    res = - val;
// { \at(val, Pre) >= 0 ==> res == val && \at(val, Pre) < 0 ==> res == -val }
  } else {
// { !(val < 0) && P }
    res = val;
// { \at(val, Pre) >= 0 ==> res == val && \at(val, Pre) < 0 ==> res == -val }
  }
// { \at(val, Pre) >= 0 ==> res == val && \at(val, Pre) < 0 ==> res == -val }

  return res;
}
```

Cependant, Hoare ne nous dit pas comment nous pouvons obtenir automatiquement la 
propriété `P` de ce programme. Ce que nous propose Dijkstra, c'est donc un moyen
de calculer, à partir d'une post-condition $Q$ et d'une commande ou d'une liste de 
commandes $C$, la pré-condition minimale assurant $Q$ après $C$. Nous pourrions 
donc, dans le programme précédent, calculer la propriété `P` qui nous donne les
garanties voulues.

Nous allons tout au long de cette partie présenter les différents cas de la 
fonction $wp$ qui, à une post-condition voulue et un programme ou une instruction,
nous associe la plus faible pré-condition qui permet de l'assurer. Nous utiliserons
cette notation pour définir le calcul correspondant à une/des instructions :

$wp(Instruction(s), Post) := WeakestPrecondition$

Et la fonction $wp$ est telle qu'elle nous garantit que le triplet de Hoare :

-> $\{\ wp(C,Q)\ \}\quad C\quad \{ Q \}$ <-

est effectivement un triplet valide. 

Nous utiliserons souvent des assertions ACSL pour présenter les notions à 
venir :

```c
//@ assert ma_propriete ;
```

Ces assertions correspondent en fait à des étapes intermédiaires possibles pour
les propriétés indiquées dans nos triplets de Hoare. Nous pouvons par exemple
reprendre le programme précédent et remplacer nos commentaires par les assertions
ACSL correspondantes (j'ai omis `P` car sa valeur est en fait simplement
« vrai ») :

```c
int abs(int val){
  int res;
  if(val < 0){
    //@ assert val < 0 ;
    res = - val;
    //@ assert \at(val, Pre) >= 0 ==> res == val && \at(val, Pre) < 0 ==> res == -val ;
  } else {
    //@ assert !(val < 0) ;
    res = val;
    //@ assert \at(val, Pre) >= 0 ==> res == val && \at(val, Pre) < 0 ==> res == -val ;
  }
  //@ assert \at(val, Pre) >= 0 ==> res == val && \at(val, Pre) < 0 ==> res == -val ;

  return res;
}
```
