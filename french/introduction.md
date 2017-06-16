[[information]]
| Le choix de certains exemples et d'une partie de l'organisation dans le présent 
| tutoriel est le même que celui du 
| [tutoriel présenté à TAP 2013](http://www.spacios.eu/TAP2013/keynotes.html) 
| par Nikolai Kosmatov, Virgile Prevosto et Julien Signoles du CEA List du fait de
| son cheminement didactique. Il contient également des exemples tirés de 
| *[ACSL By Example](http://www.fokus.fraunhofer.de/download/acsl_by_example)* 
| de Jochen Burghardt, Jens Gerlach, Kerstin Hartig, Hans Pohl et Juan Soto du 
| Fraunhofer. Le reste vient de mon expérience personnelle avec Frama-C et WP.
| 
| Le seul pré-requis pour ce cours est d'avoir une connaissance basique du 
| langage C, au moins jusqu'à la notion de pointeur.

Malgré son ancienneté, le C est un langage de programmation encore largement 
utilisé. Il faut dire qu'il n'existe, pour ainsi dire aucun langage qui soit 
disponible sur une aussi large variété de plateformes (matérielles et 
logicielles) différentes, que son orientation bas-niveau et les années 
d'optimisations investies dans ses compilateurs permettent de générer à 
partir de programme C des exécutables très performants (à condition bien sûr 
que le code le permette), et qu'il possède un nombre d'experts (et donc une 
base de connaissances) très conséquent.

De plus, de très nombreux systèmes reposent sur des quantités phénoménales de
code historiquement écrit en C, qu'il faut maintenir et corriger car ils 
coûteraient bien trop chers à redévelopper.

Mais toute personne qui a déjà codé en C sait également que c'est un langage 
très difficile à maîtriser parfaitement. Les raisons sont multiples mais les 
ambiguïtés présentes dans sa norme et la permissivité extrême qu'il offre au 
développeur, notamment en ce qui concerne les accès à la mémoire, font que 
créer un programme C robuste est très difficile même pour un programmeur 
chevronné.

Pourtant, C est souvent choisi comme langage de prédilection pour la 
réalisation de systèmes demandant un niveau critique de sûreté (aéronautique, 
ferroviaire, armement, ...) où il est apprécié pour ses performances, sa 
maturité technologique et la prévisibilité de sa compilation.

Dans ce genre de cas, les besoins de couverture par le test deviennent 
colossaux. Et, plus encore, la question « avons-nous suffisamment testé ? » 
devient une question à laquelle il est de plus en plus difficile de répondre.
C'est là qu'intervient la preuve de programme. Plutôt que tester toutes les 
entrées possibles et (in)imaginables, nous allons prouver « mathématiquement »
qu'aucun problème ne peut apparaître à l'exécution.

L'objet de ce tutoriel est d'utiliser Frama-C, un logiciel développé au 
CEA List, et WP, son greffon de preuve déductive, pour s'initier à la preuve 
de programmes C. Au delà de l'usage de l'outil en lui-même, le but de ce tutoriel
est de convaincre que nous pouvons de plus en plus souvent toucher du 
doigt l'idée qu'il est possible d'écrire des programmes sans erreurs de 
programmation, mais également de sensibiliser à des notions simples 
permettant de mieux comprendre et de mieux écrire les programmes.

[[information]]
| Merci aux différents bêta-testeurs pour leurs remarques constructives :
| 
| - [Taurre](https://zestedesavoir.com/membres/voir/Taurre/) (l'exemple en section 
| III - 3 - 4 a honteusement été copié d'un de ses posts).
| - [barockobamo](https://zestedesavoir.com/membres/voir/barockobamo/)
| - [Vayel](https://zestedesavoir.com/membres/voir/Vayel/)
|
| Ainsi qu'aux validateurs qui ont encore permis d'améliorer la qualité de ce tutoriel :
|
| - [Taurre](https://zestedesavoir.com/membres/voir/Taurre/) (oui, encore lui)
| - [Saroupille](https://zestedesavoir.com/membres/voir/Saroupille/)
|
| Finalement, un grand merci à Jens Gerlach pour son aide lors de la traduction
| anglaise du tutoriel.