# Affectation

L'affectation est l'opération la plus basique que l'on puisse avoir dans un 
langage (mise à part l'opération « ne rien faire » qui manque singulièrement 
d'intérêt). Le calcul de plus faible pré-condition associé est le suivant : 

-> $wp(x = E , Post) := Post[x \leftarrow E]$ <-

Où la notation $P[x \leftarrow E]$ signifie « la propriété $P$ où $x$ est remplacé
par $E$ ». Ce qui correspond ici à « la post-condition $Post$ où $x$ a été
remplacé par $E$ ». Dans l'idée, pour que la formule en post-condition d'une 
affectation de $x$ à $E$ soit vraie, il faut qu'elle soit vraie en remplaçant 
chaque occurrence de $x$ dans la formule par $E$. Par exemple :

```c
// { P }
x = 43 * c ;
// { x = 258 }
```

-> $P = wp(x = 43*c , \{x = 258\}) = \{43*c = 258\}$ <-

La fonction $wp$ nous permet donc de calculer la plus faible pré-condition de
l'opération ($\{43*c = 258\}$), ce que l'on peut réécrire sous la forme d'un
triplet de Hoare :

```c
// { 43*c = 258 }
x = 43 * c ;
// { x = 258 }
```

Pour calculer la pré-condition de l'affectation, nous avons remplacé chaque 
occurrence de $x$ dans la post-condition, par la valeur $E = 43*c$ affectée.
Si notre programme était de la forme:

```c
int c = 6 ;
// { 43*c = 258 }
x = 43 * c ;
// { x = 258 }
```

Nous pourrions alors fournir la formule « $43*6 = 258$ » à notre prouveur automatique
afin qu'il détermine si cette formule peut effectivement être satisfaite. Ce à quoi
il répondrait évidemment « oui » puisque cette propriété est très simple à vérifier.
En revanche, si nous avions donné la valeur 7 pour `c`, le prouveur nous répondrait
que non, une telle formule n'est pas vraie.

Nous pouvons donc écrire la règle d'inférence pour le triplet de Hoare de 
l'affectation, où l'on prend en compte le calcul de plus faible pré-condition :

-> $\dfrac{}{\{Q[x \leftarrow E] \}\quad x = E \quad\{ Q \}}$ <-

Nous noterons qu'il n'y a pas de prémisse à vérifier. Cela veut-il dire que le
triplet est nécessairement vrai ? Oui. Mais cela ne dit pas si la pré-condition 
est respectée par le programme où se trouve l'instruction, ni que cette 
pré-condition est possible. C'est ce travail qu'effectuent ensuite les prouveurs
automatiques.

Par exemple, nous pouvons demander la vérification de la ligne suivante avec 
Frama-C :

```c
int a = 42;
//@ assert a == 42;
```

Ce qui est, bien entendu, prouvé directement par Qed car c'est une simple 
application de la règle de l'affectation.

[[information]]
| Notons que d'après la norme C, l'opération d'affectation est une expression
| et non une instruction. C'est ce qui nous permet par exemple d'écrire 
| `if( (a = foo()) == 42)`. Dans Frama-C, une affectation sera toujous une
| instruction. En effet, si une affectation est présente au sein d'une 
| expression plus complexe, le module de création de l'arbre de syntaxe abstraite
| du programme analysé effectue une étape de normalisation qui crée 
| systématiquement une instruction séparée.

# Séquence d'instructions

Pour qu'une instruction soit valide, il faut que sa pré-condition nous 
permette, par cette instruction, de passer à la post-condition voulue. 
Maintenant, nous avons besoin d'enchaîner ce processus d'une 
instruction à une autre. L'idée est alors que la post-condition assurée par la
première instruction soit compatible avec la pré-condition demandée par la 
deuxième et que ce processus puisse se répéter pour la troisième instruction, 
etc.

La règle d'inférence correspondant à cette idée, utilisant les triplets de 
Hoare est la suivante:

-> $\dfrac{\{P\}\quad S1 \quad \{R\} \ \ \ \{R\}\quad S2 \quad \{Q\}}{\{P\}\quad S1 ;\ S2 \quad \{Q\}}$ <-

Pour vérifier que la séquence d'instructions $S1;\ S2$ (NB : où $S1$ et $S2$ 
peuvent elles-mêmes être des séquences d'instructions), nous passons par une 
propriété intermédiaire qui est à la fois la pré-condition de $S2$ et la 
post-condition de $S1$. Cependant, rien ne nous indique pour l'instant 
comment obtenir les propriétés $P$ et $R$.

Le calcul de plus faible pré-condition $wp$ nous dit simplement que la 
propriété intermédiaire $R$ est trouvée par calcul de plus faible pré-condition
de la deuxième instruction. Et que la propriété $P$ est trouvée en calculant la
plus faible pré-condition de la première instruction. La plus faible pré-condition
de notre liste d'instruction est donc déterminée comme ceci :

-> $wp(S1;\ S2 , Post) := wp(S1, wp(S2, Post) )$ <-

Le plugin WP de Frama-C fait ce calcul pour nous, c'est pour cela que nous 
n'avons pas besoin d'écrire les assertions entre chaque ligne de code. 

```c
int main(){
  int a = 42;
  int b = 37;

  int c = a+b; // i:1
  a -= c;      // i:2
  b += a;      // i:3

  //@assert b == 0 && c == 79;
}
```

## Arbre de preuve

Notons que lorsque nous avons plus de deux instructions, nous pouvons simplement
considérer que la dernière instruction est la seconde instruction de notre règle
et que toutes les instructions qui la précède forment la première « instruction ». 
De cette manière nous remontons bien les instructions une à une dans notre
raisonnement, par exemple avec le programme précédent :

+-------------------------------------------+------------------------------------------------+---------------------------------------------+
| -> $\{P\}\quad i_1 ; \quad \{Q_{-2}\}$ <- | -> $\{Q_{-2}\}\quad i_2 ; \quad \{Q_{-1}\}$ <- |                                             |
+-------------------------------------------+------------------------------------------------+---------------------------------------------+
| -> $\{P\}\quad i_1 ; \quad i_2 ; \quad \{Q_{-1}\}$ <-                                      | -> $\{Q_{-1}\} \quad i_3 ; \quad \{Q\}$ <-  |
+--------------------------------------------------------------------------------------------+---------------------------------------------+
| -> $\{P\}\quad i_1 ; \quad i_2 ; \quad i_3 ; \quad \{ Q \}$ <-                                                                           |
+------------------------------------------------------------------------------------------------------------------------------------------+

Nous pouvons par calcul de plus faibles pré-conditions construire la propriété
$Q_{-1}$ à partir de $Q$ et $i_3$, ce qui nous permet de déduire $Q_{-2}$, à 
partir de $Q_{-1}$ et $i_2$ et finalement $P$ avec $Q_{-2}$ et $i_1$.

Nous pouvons maintenant vérifier des programmes comprenant plusieurs 
instructions, il est temps d'y ajouter un peu de structure.

# Règle de la conditionnelle

Pour qu'un branchement conditionnel soit valide, il faut que la post-condition
soit atteignable par les deux banches, depuis la même pré-condition, à ceci 
près que chacune des branches aura une information supplémentaire : le fait 
que la condition était vraie dans un cas et fausse dans l'autre.

Comme avec la séquence d'instructions, nous aurons donc deux points à vérifier
(pour éviter de confondre les accolades, j'utilise la syntaxe 
$if\ B\ then\ S1\ else\ S2$) :

-> $\dfrac{\{P \wedge B\}\quad S1\quad \{Q\} \quad \quad \{P \wedge \neg B\}\quad S2\quad \{Q\}}{\{P\}\quad if\quad B\quad then\quad S1\quad else\quad S2 \quad \{Q\}}$ <-

Nos deux prémisses sont donc la vérification que lorsque nous avons la 
pré-condition et que nous passons dans la branche `if`, nous atteignons bien la
post-condition, et que lorsque nous avons la pré-condition et que nous passons
dans la branche `else`, nous obtenons bien également la post-condition.

Le calcul de pré-condition de $wp$ pour la conditionnelle est le suivant :

-> $wp(if\ B\ then\ S1\ else\ S2 , Post) := (B \Rightarrow wp(S1, Post)) \wedge (\neg B \Rightarrow wp(S2, Post))$ <-

À savoir que $B$ doit impliquer la pré-condition la plus faible de $S1$, pour 
pouvoir l'exécuter sans erreur vers la post-condition, et que $\neg B$ doit 
impliquer la pré-condition la plus faible de $S2$ (pour la même raison).

## Bloc `else` vide

En suivant cette définition, si le ```else``` ne fait rien, alors la règle
d'inférence est de la forme suivante, en remplaçant $S2$ par une instruction
« ne rien faire ».

-> $\dfrac{\{P \wedge B\}\quad S1\quad \{Q\} \quad \quad \{P \wedge \neg B\}\quad skip\quad \{Q\}}{\{P\}\quad if\quad B\quad then\quad S1\quad else\quad skip \quad \{Q\}}$ <-

Le triplet pour le ```else``` est :

-> $\{P \wedge \neg B\}\quad skip\quad \{Q\}$ <-

Ce qui veut dire que nous devons avoir :

-> $P \wedge \neg B \Rightarrow Q$ <-

En résumé, si la condition du `if` est fausse, cela veut dire que la 
post-condition de l'instruction conditionnelle globale est déjà vérifiée avant de 
rentrer dans le `else` (puisqu'il ne fait rien).

Par exemple, nous pourrions vouloir remettre une configuration $c$ à une valeur 
par défaut si elle a mal été configurée par un utilisateur du programme :

```c
int c;

// ... du code ...

if(c < 0 || c > 15){
  c = 0;
}
//@ assert 0 <= c <= 15;
```

Soit :

$wp(if \neg (c \in [0;15])\ then\ c := 0, \{c \in [0;15]\})$

$:= (\neg (c \in [0;15])\Rightarrow wp(c := 0, \{c \in [0;15]\})) \wedge (c \in [0;15]\Rightarrow wp(skip, \{c \in [0;15]\}))$

$= (\neg (c \in [0;15]) \Rightarrow 0 \in [0;15]) \wedge (c \in [0;15] \Rightarrow c \in [0;15])$

$= (\neg (c \in [0;15]) \Rightarrow true) \wedge true$

La formule est bien vérifiable : quelle que soit l'évaluation de $\neg (c \in [0;15])$ l'implication sera vraie.
