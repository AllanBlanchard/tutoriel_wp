Le principe d'un contrat de fonction est de poser les conditions selon 
lesquelles la fonction va s'exécuter. C'est-à-dire : ce que doit respecter 
le code appelant à propos des variables passées en paramètres et de l'état de
la mémoire globale pour que la fonction s'exécute correctement, 
**la pré-condition** ; et ce que s'engage à respecter la fonction en retour
à propos de l'état de la mémoire et de la valeur de retour : 
**la post-condition**.

Ces propriétés sont exprimées en langage ACSL, la syntaxe est relativement 
simple pour qui a déjà fait du C puisqu'elle reprend la syntaxe des expressions
booléennes du C. Cependant, elle ajoute également :

- certaines constructions et connecteurs logiques qui ne sont pas présents 
  originellement en C pour faciliter l'écriture ;
- des prédicats pré-implémentés pour exprimer des propriétés souvent utiles 
  en C (par exemple : pointeur valide) ; 
- ainsi que des types plus généraux que les types primitifs du C, 
  typiquement les types entiers ou réels. 

Nous introduirons au fil du tutoriel les notations présentes dans le 
langage ACSL.

Les spécifications ACSL sont introduites dans nos codes source par 
l'intermédiaire d'annotations. Syntaxiquement, un contrat de fonction est 
intégré dans les sources de la manière suivante :

```c
/*@
  //contrat
*/
void foo(int bar){

}
```

Notons bien le `@` à la suite du début du bloc de commentaire, c'est lui qui 
fait que ce bloc devient un bloc d'annotations pour Frama-C et pas un simple 
bloc de commentaires à ignorer.

Maintenant, regardons comment sont exprimés les contrats, à commencer par la
post-condition, puisque c'est ce que nous attendons en priorité de notre 
programme (nous nous intéresserons ensuite aux pré-conditions).

# Post-condition

La post-condition d'une fonction est précisée avec la clause ```ensures```. 
Nous allons travailler avec la fonction suivante qui donne la valeur absolue
d'un entier reçu en entrée. 
Une de ses post-conditions est que le résultat (que nous notons avec le 
mot-clé ```\result```) est supérieur ou égal à 0.

```c
/*@
  ensures \result >= 0;
*/
int abs(int val){
  if(val < 0) return -val;
  return val;
}
```

(Notons le ```;``` à la fin de la ligne de spécification comme en C).

Mais ce n'est pas tout, il faut également spécifier le comportement général 
attendu d'une fonction renvoyant la valeur absolue. À savoir : si la valeur
est positive ou nulle, la fonction renvoie la même valeur, sinon elle renvoie 
l'opposée de la valeur.

Nous pouvons spécifier plusieurs post-conditions, soit en les composants avec 
un ```&&``` comme en C, soit en introduisant une nouvelle clause ```ensures```, 
comme illustré ci-dessous.

```c
/*@
  ensures \result >= 0;
  ensures (val >= 0 ==> \result == val ) && 
          (val <  0 ==> \result == -val);
*/
int abs(int val){
  if(val < 0) return -val;
  return val;
}
```

Cette spécification est l'opportunité de présenter un connecteur logique 
très utile que propose ACSL mais qui n'est pas présent en C : 
l'implication $A \Rightarrow B$, que l'on écrit en ACSL ```A ==> B```.
La table de vérité de l'implication est la suivante :

$A$ | $B$ | $A \Rightarrow B$
----|-----|-------------------
$F$ | $F$ | $V$
$F$ | $V$ | $V$
$V$ | $F$ | $F$
$V$ | $V$ | $V$

Ce qui veut dire qu'une implication $A \Rightarrow B$ est vraie dans deux cas : 
soit $A$ est fausse (et dans ce cas, il ne faut pas se préoccuper de $B$), soit 
$A$ est vraie et alors $B$ doit être vraie aussi. L'idée étant finalement « je 
veux savoir si dans le cas où $A$ est vrai, $B$ l'est aussi. Si $A$ est faux, 
je considère que l'ensemble est vrai ».

Sa cousine l'équivalence $A \Leftrightarrow B$ (écrite ```A <==> B``` en ACSL)
est plus forte. C'est la conjonction de l'implication dans les deux sens :
$(A \Rightarrow B) \wedge (B \Rightarrow A)$. Cette formule n'est vraie que
dans deux cas : $A$ et $B$ sont vraies toutes les deux, ou fausses 
toutes les deux (c'est donc la négation du ou-exclusif).

[[information]]
| Profitons en pour rappeler l'ensemble des tables de vérités des opérateurs
| usuels en logique du premier ordre ($\neg$ = `!`, $\wedge$ = `&&`,
| $\vee$ = `||`) :
|
| $A$ | $B$ | $\neg A$ | $A \wedge B$ | $A \vee B$ | $A \Rightarrow B$ | $A \Leftrightarrow B$
| ----|-----|----------|--------------|------------|-------------------|-----------------------
| $F$ | $F$ | $V$      | $F$          | $F$        | $V$               | $V$
| $F$ | $V$ | $V$      | $F$          | $V$        | $V$               | $F$
| $V$ | $F$ | $F$      | $F$          | $V$        | $F$               | $F$
| $V$ | $V$ | $F$      | $V$          | $V$        | $V$               | $V$

Revenons à notre spécification. Quand nos fichiers commencent à être longs et 
contenir beaucoup de spécifications, il peut être commode de nommer les 
propriétés que nous souhaitons vérifier. Pour cela, nous indiquons un nom (les 
espaces ne sont pas autorisées) suivi de ```:``` avant de mettre effectivement
la propriété, il est possible de mettre plusieurs « étages » de noms pour 
catégoriser nos propriétés. Par exemple nous pouvons écrire ceci :

```c
/*@
  ensures positive_value: function_result: \result >= 0;
  ensures (val >= 0 ==> \result == val) && 
          (val < 0 ==> \result == -val);
*/
int abs(int val){
  if(val < 0) return -val;
  return val;
}
```

Dans une large part du tutoriel, nous ne nommerons pas les éléments que nous 
tenterons de prouver, les propriétés seront généralement relativement simples
et peu nombreuses, les noms n'apporteraient pas beaucoup d'information.

Nous pouvons copier/coller la fonction ```abs``` et sa spécification dans un 
fichier abs.c et regarder avec Frama-C si l'implémentation est conforme à la 
spécification.

Pour cela, il faut lancer l'interface graphique de Frama-C (il est également 
possible de se passer de l'interface graphique, cela ne sera pas présenté
dans ce tutoriel) soit par cette commande :

```bash
$ frama-c-gui
```

Soit en l'ouvrant depuis l'environnement graphique. 

Il est ensuite possible de cliquer sur le bouton « *Create a new session from 
existing C files* », les fichiers à analyser peuvent être sélectionnés par
double-clic, OK terminant la sélection. Par la suite, l'ajout d'autres 
fichiers à la session s'effectue en cliquant sur Files > Source Files. 

À noter également qu'il est possible de directement ouvrir le(s) fichier(s) 
depuis la ligne de commande en le(s) passant en argument(s) de ```frama-c-gui```.

```bash
$ frama-c-gui abs.c
```

![Le volet latéral liste l’arbre des fichiers et des fonctions](https://zestedesavoir.com:443/media/galleries/2584/dab8888e-32fc-4856-bb87-4de884829822.png)

La fenêtre de Frama-C s'ouvre, dans le volet correspondant aux fichiers et aux
fonctions, nous pouvons sélectionner la fonction ```abs```. 
Aux différentes lignes ```ensures```, il y a un cercle bleu dans la marge, ils 
indiquent qu'aucune vérification n'a été tentée pour ces lignes.

Nous demandons la vérification que le code répond à la spécification en faisant 
un clic droit sur le nom de la fonction et « *Prove function annotations by WP* » :

![Lancer la vérification de ```abs``` avec WP](https://zestedesavoir.com:443/media/galleries/2584/ed44f0d3-763f-423e-8a01-a9be7aace0d3.png)

Nous pouvons voir que les cercles bleus deviennent des pastilles vertes, 
indiquant que la spécification est bien assurée par le programme. Il est 
possible de prouver les propriétés une à une en cliquant droit sur celles-ci 
et pas sur le nom de la fonction.

Mais le code est-il vraiment sans erreur pour autant ? WP nous permet de nous 
assurer que le code répond à la spécification, mais il ne fait pas de contrôle 
d'erreur à l'exécution (RunTime Error : RTE). C'est le rôle d'un autre petit 
plugin que nous allons utiliser ici et qui s'appelle sobrement RTE. Son but est
d'ajouter des contrôles dans le programme pour les erreurs d'exécutions 
possibles (débordements d'entiers, déréférencements de pointeurs invalides, 
division par 0, etc). 

Pour activer ce contrôle, nous cochons la case montrée par cette capture (dans 
le volet de WP). Il est également possible de demander à Frama-C d'ajouter ces 
contrôles par un clic droit sur le nom de la fonction puis « Insert RTE guards ».

![Activer la vérification des erreurs d'exécution](https://zestedesavoir.com:443/media/galleries/2584/bae7515e-8841-4a27-9253-e1bf26eb0d81.png)

Enfin nous relançons la vérification (nous pouvons également cliquer sur le 
bouton « *Reparse* » de la barre d'outils, cela aura pour effet de supprimer les
preuves déjà effectuées).

Nous pouvons alors voir alors que WP échoue à prouver  l'impossibilité de 
débordement arithmétique sur le calcul de -val. Et c'est bien normal parce 
que -```INT_MIN``` ($-2^{31}$) > ```INT_MAX``` ($2^{31}-1$).

![Preuve incomplète de ```abs```](https://zestedesavoir.com:443/media/galleries/2584/ec869f49-9193-4896-a490-9549f256a639.png)

[[information]]
| Il est bon de noter que le risque de dépassement est pour nous réel car nos
| machines (dont Frama-C détecte la configuration) fonctionne en 
| [complément à deux](https://fr.wikipedia.org/wiki/Compl%C3%A9ment_%C3%A0_deux)
| pour lequel le dépassement n'est pas défini par la norme C.

Ici nous pouvons voir un autre type d'annotation ACSL. La 
ligne ```//@ assert propriete ;``` nous permet de demander la vérification 
d'une propriété à un point particulier du programme. Ici, l'outil l'a 
insérée pour nous car il faut vérifier que le ```-val``` ne provoque pas de 
débordement, mais il est également possible d'en ajouter manuellement dans 
un code.

Comme le montre cette capture d'écran, nous avons deux nouveaux codes couleur
pour les pastilles : vert+marron et orange. 

La couleur vert + marron nous indique que la preuve a été effectué mais 
qu'elle dépend potentiellement de propriétés qui, elle, ne l'ont pas été. 

Si  la preuve n'est pas recommencée intégralement par rapport à la preuve 
précédente, ces pastilles ont dû rester vertes car les preuves associées ont
été réalisées avant l'introduction de la propriété nous assurant l'absence 
de runtime-error, et ne se sont donc pas reposées sur la connaissance de cette
propriété puisqu'elle n'existait pas.

En effet, lorsque WP transmet une obligation de preuve à un prouveur automatique,
il transmet (basiquement) deux types de propriétés : $G$, le but, la propriété 
que l'on cherche à prouver, et $S_1$ ... $S_n$ les diverses suppositions que l'on
peut faire à propos de l'état du programme au point où l'on cherche à vérifier $G$.
Cependant, il ne reçoit pas, en retour, quelles propriétés ont été utilisées par
le prouveur pour valider $G$. Donc si $S_3$ fait partie des suppositions, et si
WP n'a pas réussi à obtenir une preuve de $S_3$, il indique que $G$ est vraie, mais
à condition seulement que l'on arrive un jour à prouver $S_3$.

La couleur orange nous signale qu'aucun prouveur n'a pu déterminer si la 
propriété est vérifiable. Les deux raisons peuvent être :

- qu'il n'a pas assez d'information pour le déterminer ;
- que malgré toutes ses recherches, il n'a pas pu trouver un résultat à 
  temps. Auquel cas, il rencontre un *timeout* dont la durée est configurable 
  dans le volet de WP.

Dans le volet inférieur, nous pouvons sélectionner l'onglet « *WP Goals* », 
celui-ci nous affiche la liste des obligations de preuve et pour chaque 
prouveur indique un petit logo si la preuve a été tentée et si elle a été 
réussie, échouée ou a rencontré un *timeout* (ici nous pouvons voir un essai 
avec Z3 sur le contrôle de la RTE pour montrer le logo des ciseaux 
associé au timeout).

![Tableau des obligations de preuve de WP pour ```abs```](https://zestedesavoir.com:443/media/galleries/2584/d1c2dded-1e12-4cee-a575-7c990274f5c4.png)

Le tableau est découpé comme suit, en première colonne nous avons le nom de la
fonction où se trouve le but à prouver. En seconde colonne nous trouvons le nom
du but. Ici par exemple notre post-condition nommée est estampillée 
"Post-condition 'positive_value,function_result'", nous pouvons d'ailleurs noter
que lorsqu'une propriété est sélectionnée dans le tableau, elle est également 
sur-lignée dans le code source. Les propriétés non-nommées se voient assignées
comme nom le type de propriété voulu. En troisième colonne, nous trouvons le 
modèle mémoire utilisé pour la preuve, (nous n'en parlerons pas dans ce 
tutoriel). Finalement, les dernières colonnes représentent les différents 
prouveurs accessibles à WP.

Dans ces prouveurs, le premier élément de la colonne est Qed. Ce n'est pas
à proprement parler un prouveur. En fait, si nous double-cliquons sur la 
propriété "ne pas déborder" (surlignée en bleu dans la capture précédente), 
nous pouvons voir ceci :

![Obligation de preuve associée à la vérification de débordement dans ```abs```](https://zestedesavoir.com:443/media/galleries/2584/cf50837e-a119-40f9-8c93-c2b0bb03a142.png)

C'est l'obligation de preuve que génère WP par rapport à notre propriété et 
notre programme, il n'est pas nécessaire de comprendre tout ce qui s'y passe, 
juste d'avoir une idée globale. Elle contient (dans la partie « *Assume* ») les 
suppositions que nous avons pu donner et celles que WP a pu déduire des 
instructions du programme. Elle contient également (dans la partie « *Prove* ») 
la propriété que nous souhaitons vérifier.

Que fait WP avec ces éléments ? En fait, il les transforme en une formule 
logique puis demande aux différents prouveurs s'il est possible de la 
satisfaire (de trouver pour chaque variable, une valeur qui rend la formule 
vraie), cela détermine si la propriété est prouvable. Mais avant d'envoyer 
cette formule aux prouveurs, WP utilise un module qui s'appelle Qed et qui est
capable de faire différentes simplifications à son sujet. Parfois comme dans 
le cas des autres propriétés de ```abs```, ces simplifications suffisent à 
déterminer que la propriété est forcément vraie, auquel cas, nous ne faisons
pas appel aux prouveurs.

Lorsque les prouveurs automatiques ne parviennent pas à assurer que nos 
propriétés sont bien vérifiées, il est parfois difficile de comprendre 
pourquoi. En effet, les prouveurs ne sont généralement pas capables de nous 
répondre autre chose que « oui », « non » ou « inconnu », ils ne sont pas capables
d'extraire le « pourquoi » d'un « non » ou d'un « inconnu ». Il existe des outils qui
sont capables d'explorer les arbres de preuve pour en extraire ce type 
d'information, Frama-C n'en possède pas à l'heure actuelle. La lecture des
obligations de preuve peut parfois nous aider, mais cela demande un peu 
d'habitude pour pouvoir les déchiffrer facilement. Finalement, le meilleur
moyen de comprendre la raison d'un échec est d'effectuer la preuve de manière
interactive avec Coq. En revanche, il faut déjà avoir une certaine habitude de
ce langage pour ne pas être perdu devant les obligations de preuve générées par
WP, étant donné que celles-ci encodent les éléments de la sémantique de C, ce 
qui rend le code souvent indigeste.

Si nous retournons dans notre tableau des obligations de preuve (bouton 
encadré dans la capture d'écran précédente), nous pouvons donc voir que les 
hypothèses n'ont pas suffi aux prouveurs pour déterminer que la propriété 
« absence de débordement » est vraie (et nous l'avons dit : c'est normal), il 
nous faut donc ajouter une hypothèse supplémentaire pour garantir le bon 
fonctionnement de la fonction : une pré-condition d'appel.

# Pré-condition

Les pré-conditions de fonctions sont introduites par la clause ```requires```,
de la même manière qu'avec ```ensures```, nous pouvons composer nos 
expressions logiques et mettre plusieurs pré-conditions :

```c
/*@
  requires 0 <= a < 100;
  requires b < a;
*/
void foo(int a, int b){
  
}
```

Les pré-conditions sont des propriétés sur les entrées (et potentiellement sur
des variables globales) qui seront supposées préalablement vraies lors de 
l'analyse de la fonction. La preuve que celles-ci sont effectivement validées 
n'interviendra qu'aux points où la fonction est appelée.

Dans ce petit exemple, nous pouvons également noter une petite différence avec 
C dans l'écriture des expressions booléennes. Si nous voulons spécifier 
que ```a``` se trouve entre 0 et 100, il n'y a pas besoin d'écrire ```0 <= a && a < 100```
(c'est-à-dire en composant les deux comparaisons avec un ```&&```). Nous 
pouvons simplement écrire ```0 <= a < 100``` et l'outil se chargera de faire
la traduction nécessaire.

Si nous revenons à notre exemple de la valeur absolue, pour éviter le 
débordement arithmétique, il suffit que la valeur de val soit strictement 
supérieure à ```INT_MIN``` pour garantir que le débordement n'arrivera pas.
Nous l'ajoutons donc comme pré-condition (à noter : il faut également
inclure le header où ```INT_MIN``` est défini) :

```c
#include <limits.h>

/*@
  requires INT_MIN < val;

  ensures \result >= 0;
  ensures (val >= 0 ==> \result == val) && 
          (val < 0 ==> \result == -val);
*/
int abs(int val){
  if(val < 0) return -val;
  return val;
}
```

[[attention]]
| Rappel : la fenêtre de Frama-C ne permet pas l'édition du code source.

[[information]]
| Avec les versions de Frama-C NEON et plus anciennes, le pré-processing des
| annotations n'était pas activé par défaut. Il faut donc lancer Frama-C avec
| l'option `-pp-annot` :
| ```bash
| $ frama-c-gui -pp-annot file.c
| ```

Une fois le code source modifié de cette manière, un clic sur « *Reparse* » et 
nous lançons à nouveau l'analyse. Cette fois, tout est validé pour WP, notre 
implémentation est prouvée :

![Preuve de ```abs``` effectuée](https://zestedesavoir.com:443/media/galleries/2584/07785936-5148-406d-a432-5e88e4f25328.png)

Nous pouvons également vérifier qu'une fonction qui appellerait ```abs``` 
respecte bien la pré-condition qu'elle impose :

```c
void foo(int a){
   int b = abs(42);
   int c = abs(-42);
   int d = abs(a);       // Faux : "a", vaut peut être INT_MIN
   int e = abs(INT_MIN); // Faux : le paramètre doit être strictement supérieur à INT_MIN
}
```

![Vérification du contrat à l'appel de ```abs```](https://zestedesavoir.com:443/media/galleries/2584/12a9ba65-5934-4d3e-bb52-d273d90fcf98.png)

Pour modifier un peu l'exemple, nous pouvons essayer d'inverser les deux 
dernières lignes. Auquel cas, nous pouvons voir que l'appel ```abs(a)```
est validé par WP s'il se trouve après l'appel ```abs(INT_MIN)``` ! 
Pourquoi ?

Il faut bien garder en tête que le principe de la preuve déductive est de nous
assurer que si les pré-conditions sont vérifiées et que le calcul termine alors
la post-condition est vérifiée.

Si nous donnons à notre fonction une valeur qui viole ses pré-conditions, alors
nous en déduisons que la post-condition est fausse. À partir de là, nous pouvons 
prouver tout ce que nous voulons car ce « false » devient une supposition pour
tout appel qui viendrait ensuite. À partir de faux, nous prouvons tout ce que 
nous voulons, car si nous avons la preuve de « faux » alors « faux » est vrai, de 
même que « vrai » est vrai. Donc tout est vrai.

En prenant le programme modifié, nous pouvons d'ailleurs regarder les obligations
de preuve générées par WP pour l'appel fautif et l'appel prouvé par conséquent :

![Obligation générée pour l'appel fautif](https://zestedesavoir.com:443/media/galleries/2584/997f0ae1-bd5a-45b5-a24f-56cbf934eb5f.png)

![Obligation générée pour l'appel qui suit](https://zestedesavoir.com:443/media/galleries/2584/f81582b8-e822-47c5-9600-ee34b0d04a21.png)

Nous pouvons remarquer que pour les appels de fonctions, l'interface graphique
nous surligne le chemin d'exécution suivi avant l'appel dont nous cherchons à 
vérifier la pré-condition. Ensuite, si nous regardons l'appel ```abs(INT_MIN)```,
nous pouvons remarquer qu'à force de simplifications, Qed a déduit que nous 
cherchons à prouver « False ». Conséquence logique, l'appel suivant ```abs(a)``` 
reçoit dans ses suppositions « False ». C'est pourquoi Qed est capable de déduire
immédiatement « True ». 

La deuxième partie de la question est alors : pourquoi lorsque nous mettons les 
appels dans l'autre sens (```abs(a)``` puis ```abs(INT_MIN)```), nous obtenons 
quand même une violation de la pré-condition sur le deuxième ? La réponse est 
simplement que ```abs(a)``` peut, ou ne peut pas, provoquer une erreur, alors 
que ```abs(INT_MIN)``` provoque forcément l'erreur. Donc si nous obtenons 
nécessairement une preuve de « faux » avec un appel ```abs(INT_MIN)```, ce n'est
pas le cas de l'appel ```abs(a)``` qui peut aussi ne pas échouer.

Bien spécifier son programme est donc d'une importance cruciale. Typiquement, 
préciser une pré-condition fausse peut nous donner la possibilité de prouver 
FAUX :

```c
/*@
  requires a < 0 && a > 0;
  ensures  \false;
*/
void foo(int a){

}
```

Si nous demandons à WP de prouver cette fonction. Il l'acceptera sans rechigner
car la supposition que nous lui donnons en entrée est nécessairement fausse. Par
contre, nous aurons bien du mal à lui donner une valeur en entrée qui respecte la 
pré-condition, nous pourrons donc nous en apercevoir. En regardant pourquoi nous
n'arrivons pas à transmettre une valeur valide en entrée. 

Certaines notions que nous verrons plus loin dans le tutoriel apporterons un 
risque encore plus grand de créer ce genre d'incohérence. Il faut donc toujours
avoir une attention particulière pour ce que nous spécifions.

## Trouver les bonnes pré-conditions

Trouver les bonnes pré-conditions à une fonction est parfois difficile. Le plus
important est avant tout de déterminer ces pré-conditions sans prendre en compte
le contenu de la fonction (au moins dans un premier temps) afin d'éviter de 
construire, par erreur, une spécification qui contiendrait le même bug qu'un code
fautif, par exemple en prenant en compte une condition faussée. C'est pour cela que
l'on souhaitera généralement que la personne qui développe le programme et la 
personne qui le spécifie formellement soient différentes (même si elles ont pu
préalablement s'accorder sur une spécification textuelle par exemple).

Une fois ces pré-conditions posées, alors seulement, nous nous intéressons aux
spécifications dues au fait que nous sommes soumis aux contraintes de notre langage
et notre matériel. Par exemple, la fonction valeur absolue n'a, au fond, pas 
vraiment de pré-condition à respecter, c'est la machine cible qui détermine qu'une
condition supplémentaire doit être respectée en raison du complément à deux.

# Quelques éléments sur l'usage de WP et Frama-C

Dans les deux sous-sections précédentes, nous avons vu un certain nombre 
d'éléments à propos de l'usage de la GUI pour lancer les preuves. En fait, 
il est possible de demander immédiatement à WP d'effectuer les preuves pendant
le lancement de Frama-C avec la commande :

```bash
$ frama-c-gui file.c -wp
```

Cela demande à WP d'immédiatement faire les calculs de plus faible pré-condition
et de lancer les prouveurs sur les buts générés.

Concernant les contrôles des RTE, il est généralement conseillé de commencer par
vérifier le programme sans mettre les contrôles de RTE. Et ensuite seulement de
générer les assertions correspondantes pour terminer la vérification avec WP. 
Cela permet à WP de se « concentrer » dans un premier temps sur les propriétés 
fonctionnelles sans avoir la connaissance de propriétés purement techniques dues
à C, qui chargent inutilement la base de connaissances. Une nouvelle fois, il est
possible de produire ce comportement directement depuis la ligne de commande en
écrivant :

```bash
$ frama-c-gui file.c -wp -then -rte -wp
```

« Lancer Frama-C avec WP, puis créer les assertions correspondant aux RTE, et 
lancer à nouveau WP ».
