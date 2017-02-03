[[information]]
| Cette partie est plus formelle que ce nous avons vu jusqu'à maintenant. Si le 
| lecteur souhaite se concentrer sur l'utilisation de l'outil, l'introduction de
| ce chapitre et les deux premières sections (sur les instructions de base et "le 
| bonus stage") sont dispensables. Si ce que nous avons présenté jusqu'à maintenant
| vous a semblé ardu sur un plan formel, il est également possible de réserver 
| l'introduction et ces deux sections pour une deuxième lecture.
| 
| Les sections sur les boucles sont en revanches indispensables. Les éléments plus
| formels de ces sections seront signalés.

Pour chaque notion en programmation C, Nous associerons la règle d'inférence qui 
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

Inversement, pour prouver qu'une certaine prémisse est vraie, il peut etre nécessaire d'utiliser une autre règle d'inférence, ce qui nous donnerait quelque
chose comme :

-> $\dfrac{\dfrac{}{\quad P_1\quad} \quad \dfrac{P_{n_1}\quad P_{n_2}}{P_n}}{C}$ <-

Ce qui nous construit progressivement l'arbre de déduction de notre raisonnement.
Dans notre raisonnement, les prémisses et conclusions manipulées seront 
généralement des triplets de Hoare.

# Triplet de Hoare

Revenons sur la notion de triplet de Hoare :

-> $\{ P \} C \{ Q \}$ <-

Nous l'avons vu en début de tutoriel, ce que nous propose Dijkstra, c'est un moyen 
de calculer à partir d'une post-condition $Q$ et d'une commande ou d'une liste de
commandes $C$, la pré-condition minimale assurant $Q$ après $C$. Plus formellement, l'idée est la suivante :

-> $\{\ wp(C,Q)\ \} C \{ Q \}$ <-

Nous pouvons considérer que $wp$ est une fonction qui, à une post-condition voulue 
et un programme ou une instruction, nous associe la plus faible pré-condition qui
permet de l'assurer. Nous utiliserons donc cette notation pour définir le calcul
correspondant à une/des instructions :

$wp(Instruction(s), Post) = WeakestPrecondition$

Nous utiliserons souvent des assertions ACSL pour présenter les notions à 
venir :

```c
//@ assert ma_propriete ;
```
