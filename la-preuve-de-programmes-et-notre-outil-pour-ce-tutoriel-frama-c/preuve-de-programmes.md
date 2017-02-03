# Assurer la conformité des logiciels

Assurer qu'un programme a un comportement conforme à celui que nous attendons
est souvent une tâche difficile. Plus en amont encore, il est déjà complexe 
d'établir sur quel critère nous pouvons estimer que le programme "fonctionne" :

- les débutants "essayent" simplement leurs programmes et estiment qu'ils 
  fonctionnent s'ils ne plantent pas,
- les codeurs un peu plus habitués établissent quelques jeux de tests dont ils
  connaissent les résultats et comparent les sorties de leurs programmes,
- la majorité des entreprises établissent des bases de tests conséquentes, 
  couvrant un maximum de code ; tests exécutés de manière systématique sur les 
  codes de leurs bases. Certaines font du développement dirigé par le test,
- les entreprises de domaines critiques, comme l'aérospatial, le ferroviaire ou
  l'armement, passent par des certifications leur demandant de répondre à des 
  critères très stricts de codage et de couverture de code par les tests.

Et bien sûr, il existe tous les "entre-deux" dans cette liste.

Dans toutes ces manières de s'assurer qu'un programme fait ce qui est attendu, 
il y a un mot qui revient souvent : *test*. Nous *essayons* des entrées de 
programme dans le but d'isoler des cas qui poseraient problème. Nous fournissons
des entrées *estimées représentatives* de l'utilisation réelle du programme et 
nous nous assurons que les résultats attendus sont conformes. Mais nous ne 
pouvons pas *tout* tester. Nous ne pouvons pas essayer *toutes* les 
combinaisons de *toutes* les entrées possibles du programme. Toute la 
difficulté réside donc dans le fait de choisir les bons tests.

Le but de la preuve de programme est de s'assurer que, quelle que soit l'entrée
fournie au programme, si elle respecte la spécification, alors le programme 
fera ce qui est attendu. Cependant, comme nous ne pouvons pas tout essayer, nous 
allons établir formellement, mathématiquement, la preuve que le logiciel ne 
peut exhiber que les comportements qui sont spécifiés et que les erreurs 
d'exécution n'en font pas partie.

Une phrase très célèbre de Dijkstra exprime très clairement la différence entre
test et preuve :

> Program testing can be used to show the presence of bugs, but never to show 
> their absence!
Source: Dijkstra

Le test de programme peut-être utilisé pour montrer la présence de bugs mais 
jamais pour montrer leur absence.

## Le Graal du logiciel sans bug

Dans chaque nouvelle à propos d'attaque sur des systèmes informatiques, ou 
des virus, ou des bugs provoquant des crashs, il y a toujours la remarque 
séculaire "le programme inviolable/incassable/sans bugs n'existe pas". Et 
il s'avère généralement que bien qu'assez vraie, cette phrase soit assez 
mal comprise.

Outre la différence entre sûreté et sécurité (qui peut **vaguement** être 
définie par la présence d'un élément malveillant dans l'histoire), nous ne 
précisons pas ce que nous entendons par "sans bug". La création d'un logiciel
fait toujours au moins intervenir deux étapes : la rédaction de ce qui est
attendu sous la forme d'une spécification (souvent un cahier des charges) 
et la réalisation du logiciel répondant à cette spécification. Et ce sont 
également les deux moments où les erreurs peuvent être introduites.

Tout au long de ce tutoriel, nous allons nous attacher à montrer comment nous 
pouvons prouver que l'implémentation est conforme à la spécification. Mais 
quels sont les arguments de la preuve par rapport aux tests ? D'abord la preuve
est complète, elle n'oublie pas de cas s'ils sont présents dans la spécification 
(le test serait trop coûteux s'il était exhaustif). D'autre part, l'obligation 
de formaliser la spécification sous une forme logique demande de comprendre 
exactement le besoin auquel nous devons répondre.

Nous pourrions dire avec cynisme que la preuve nous montre finalement que 
l'implémentation "ne contient aucun bugs de plus que la spécification". D'une 
part, c'est un sacré pas en avant par rapport à "le test nous montre que 
l'implémentation ne contient pas beaucoup plus de bugs que la spécification". 
Et d'autre part, il existe également des techniques permettant d'analyser les 
spécifications en quête d'erreurs ou de manquements.

# Un peu de contexte

Les méthodes formelles, comme elles sont appelées, permettent dans le domaine de 
l'informatique de raisonner de manière rigoureuse, mathématique, à propos des 
programmes. Il existe un très large panel de méthodes formelles qui peuvent 
intervenir à tous les niveaux de la conception, l'implémentation, l'analyse et
la validation des programmes ou de manière plus générale de tout système
permettant le traitement de l'information.

Ici, nous allons nous intéresser à la vérification que nos programmes sont 
conformes au comportement que nous attendons de leur part. Nous allons utiliser 
des outils capables d'analyser le code et de nous dire si oui, ou non, notre 
code correspond à ce que nous voulons exprimer. La technique que nous allons 
étudier ici est une analyse statique, même s'il existe également des analyses
dynamiques notamment en ce qui concerne le monitoring de code. Le principe des 
analyses statiques est que nous n'exécuterons pas le programme pour nous assurer 
que son fonctionnement est correct, mais nous raisonnerons sur un modèle 
mathématique définissant l'ensemble des états qu'il peut atteindre.

Ce modèle peut être plus ou moins abstrait selon la technique utilisée, c'est 
donc une approximation des états possibles de notre programme. Plus l'approximation
est précise, plus le modèle est concret, plus l'approximation est large, plus il
est abstrait. Une des contraintes est bien sûr que nous ne devons jamais 
sous-approximer les comportements du programme : nous risquerions d'écarter un 
comportement qui contient une erreur. Inversement, si nous sur-approximons notre
programme, nous ajoutons des exécutions qui ne peuvent en réalité pas arriver et
si nous ajoutons trop d'exécutions inexistantes, nous pourrions ne plus être en
mesure de prouver son bon fonctionnement dans le cas où certaines d'entre elles
seraient fautives.

Dans le cas de l'outil que nous allons utiliser, le modèle est plutôt concret. 
Chaque type d'instruction, chaque type de structure de contrôle d'un programme 
se voit attribuer une sémantique, une représentation de son comportement dans 
un monde purement logique, mathématique. Le cadre logique qui nous intéresse 
ici, c'est la logique de Hoare.

# Les triplets de Hoare

La logique de Hoare est une méthode de formalisation des programmes proposée 
par Tony Hoare en 1969 dans un article intitulé *An Axiomatic Basis for 
Computer Programming* (Une base axiomatique pour la programmation des 
ordinateurs). Cette méthode définit :

- des axiomes, qui sont des propriétés que nous admettons, comme  
  "l'action 'ne rien faire' ne change pas l'état du programme",
- et des règles pour raisonner à propos des différentes possibilités de 
  compositions d'actions, par exemple "l'action 'ne rien faire' puis 'faire 
  l'action A' est équivalent à 'faire l'action A'".

Le comportement d'un programme est défini par ce que nous appelons les triplets
de Hoare :

-> $\{P\} C \{Q\}$ <-

Où $P$ et $Q$ sont des prédicats, des formules logiques qui nous disent dans 
quel état se trouve la mémoire traitée par le programme. $C$ est un ensemble de
commandes définissant un programme. Cette écriture nous dit "si nous sommes 
dans un état où $P$ est vrai, alors, après exécution de $C$ et si $C$ termine, 
alors $Q$ sera vrai pour le nouvel état du programme". Dis autrement, $P$ est 
la pré-condition nécessaire pour que $C$ nous amène à la post-condition $Q$. 
Par exemple, le triplet correspondant à l'action "ne rien faire" (**skip**) 
est le suivant :

-> $\{P\}$ **skip** $\{P\}$ <-

Quand nous ne faisons rien, la post-condition est la même que la pré-condition.

Tout au long de ce tutoriel, nous verrons la sémantique de diverses 
constructions (blocs conditionnels, boucles, etc ...) dans la logique de Hoare.
Il n'est pas nécessaire de les mémoriser ni même de comprendre toute la théorie 
derrière mais il est toujours utile d'avoir au moins une vague idée du 
fonctionnement de l'outil que nous utilisons ;) .

Tout ceci nous donne les bases permettant de dire "voilà ce que fait cette 
action" mais ne nous donne pas encore de matériel pour mécaniser la preuve. 
L'outil que nous allons utiliser repose sur la technique de calcul de plus 
faible pré-condition.

# Calcul de plus faible pré-condition

Le calcul de plus faible pré-condition est une forme de sémantique de 
transformation de prédicats, proposée par Dijkstra en 1975 dans *Guarded 
commands, non-determinacy and formal derivation of programs*.

Cette phrase contient pas mal de mots méchants mais le concept est en fait très
simple. Comme nous l'avons vu précédemment, la logique de Hoare nous donne des
règles nous expliquant comment se comportent les actions d'un programme. Mais 
elle ne nous dit pas comment appliquer ces règles pour établir une preuve 
complète du programme.

Dijkstra reformule la logique de Hoare en expliquant comment, dans le triplet 
$\{P\}C\{Q\}$, l'instruction, ou le bloc d'instruction, $C$ transforme le 
prédicat $P$, en $Q$. Cette forme est appelée "raisonnement vers l'avant" ou 
*forward-reasonning*. Nous calculons à partir d'une pré-condition et d'une ou 
plusieurs instructions, la plus forte post-condition que nous pouvons
atteindre. Informellement, en considérant ce qui est reçu en l'entrée, nous 
calculons ce qui sera renvoyé au plus en sortie. Si la post-condition voulue
est au moins aussi forte, alors nous avons prouvé qu'il n'y a pas de 
comportements non-voulus.

Par exemple :

```c
int a = 2;
a = 4;
//post-condition calculée : a == 4
//post-condition voulue   : 0 <= a <= 30
```

Pas de problème, 4 fait bien partie des valeurs acceptables pour a.

La forme qui nous intéresse, le calcul de plus faible pré-condition, fonctionne
dans le sens inverse, nous parlons de "raisonnement vers l'arrière" ou 
*backward-reasonning*. À partir de la post-condition voulue et de 
l'instruction que nous traitons, nous allons trouver la pré-condition minimale
qui nous assure ce fonctionnement. Si notre pré-condition réelle est au moins
aussi forte, c'est-à-dire, qu'elle implique la plus faible pré-condition, alors
notre programme est valide.

Par exemple, si nous avons l'instruction (sous forme de triplet) :

$\{P\}$ $x$ $:=$ a $\{x = 42\}$

Quelle est la pré-condition minimale pour que la post-condition $\{x = 42\}$ 
soit respectée ? La règle nous dira que $P$ est $\{$a$=42\}$.

Nous n'allons pas nous étendre sur ces notions pour le moment, nous y 
reviendrons au cours du tutoriel pour comprendre ce que font les outils que
nous utilisons. Et nos outils, parlons-en justement.
