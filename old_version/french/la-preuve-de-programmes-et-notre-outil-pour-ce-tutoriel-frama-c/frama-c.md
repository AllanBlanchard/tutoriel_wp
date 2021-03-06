->![](http://frama-c.com/modern/framac.gif)<-

# Frama-C ? WP ?

Frama-C (pour FRAmework for Modular Analysis of C code) est une plate-forme
 dédiée à l'analyse de programmes C créée par le CEA List et Inria. Elle est 
 basée sur une architecture modulaire permettant l'utilisation de divers 
 plugins avec ou sans collaborations. Les plugins fournis par défaut 
 comprennent diverses analyses statiques (sans exécution du code analysé), 
 dynamiques (avec exécution du code), ou combinant les deux.

Frama-C nous fournit également un langage de spécification appelé ACSL (« Axel »)
pour *ANSI C Specification Language* et qui va nous permettre d'exprimer les 
propriétés que nous souhaitons vérifier sur nos programmes. Ces propriétés seront
écrites sous forme d'annotations dans les commentaires. Pour les personnes qui 
auraient déjà utilisé Doxygen, ça y ressemble beaucoup, sauf que tout sera 
écrit sous forme de formules logiques. Tout au long de ce tutoriel, nous allons 
beaucoup parler d'ACSL donc nous ne nous étendrons pas plus à son sujet ici.

L'analyse que nous allons utiliser ici est fournie par un plugin appelé WP pour
*Weakest Precondition*, elle implémente la technique dont nous avons parlé plus tôt : 
à partir des annotations ACSL et du code source, le plugin génère ce que nous 
appelons des obligations de preuves, qui sont des formules logiques dont nous
devons vérifier la satisfiabilité. Cette vérification peut être faite de manière 
manuelle ou automatique, ici nous n'utiliserons que des outils automatiques.

Nous allons en l'occurrence utiliser un solveur de formules SMT
([statisfiabilité modulo théorie](https://fr.wikipedia.org/wiki/Satisfiability_modulo_theories),
et nous n'entrerons pas dans les détails). Ce solveur se nomme 
[Alt-Ergo](http://alt-ergo.lri.fr/), initialement développé par le Laboratoire
de Recherche en Informatique d'Orsay, aujourd'hui mis à jour et maintenu par
OCamlPro.

# Installation

Frama-C est un logiciel développé sous Linux et OSX. Son support est donc bien
meilleur sous ces derniers. Il existe quand même de quoi faire une installation 
sous Windows et en théorie l'utilisation sera sensiblement la même que sous 
Linux, mais :

[[attention]]
| - le tutoriel présentera le fonctionnement sous Linux et l'auteur n'a pas 
|   expérimenté les différences d'utilisation qui pourraient exister avec 
|   Windows,
| - La section « Bonus » un peu plus loin dans cette partie pourrait ne pas être
|   accessible.

## Linux

### Via les gestionnaires de paquets

Sous Debian, Ubuntu et Fedora, il existe des paquets pour Frama-C. Dans ce cas, 
il suffit de taper cette ligne de commande :

```bash
apt-get/yum install frama-c
```

Par contre, ces dépôts ne sont pas systématiquement à jour. En soi, ce n'est pas très gênant car il n'y a pas de nouvelle version de Frama-C tous les deux mois, mais il est tout de même bon de le savoir.

Pour vérifier l'installation, c'est dans la sous-section « Vérifier l'installation »
que les informations sont données.

### Via opam

La deuxième solution consiste à passer par Opam, un gestionnaire de paquets 
pour les bibliothèques et applications OCaml. 

D'abord Opam doit être installé et configuré sur votre distribution (voir 
leur documentation). Ensuite, il faut également que quelques paquets de votre
distribution soit présents préalablement à l'installation de Frama-C :

- lib gtk2 dev
- lib gtksourceview2 dev
- lib gnomecanvas2 dev
- (conseillé) lib zarith dev

Enfin, du côté d'Opam, il reste à installer Frama-C et Alt-Ergo.

```bash
opam install frama-c
opam install alt-ergo
```

Pour vérifier l'installation, c'est dans la sous-section « Vérifier l'installation »
que les informations sont données.

### Via compilation « manuelle »

Pour installer Frama-C via compilation manuelle, les paquets indiqués dans la 
section Opam sont nécessaires (mis à part Opam lui-même bien sûr). Il faut
également une version récente d'Ocaml et de son compilateur (y compris vers 
code natif).

Après décompression de l'archive disponible ici : 
[http://frama-c.com/download.html](http://frama-c.com/download.html) (Source distribution). 
Il faut se rendre dans le dossier et exécuter la commande :

```bash
./configure && make && sudo make install
```

Pour vérifier l'installation, c'est dans la sous-section « Vérifier l'installation »
que les informations sont données.

## OSX

L'installation sur OSX passe par Homebrew et Opam. L'auteur n'ayant
personnellement pas d'OSX, voici une honteuse paraphrase du guide 
d'installation de Frama-C pour OSX.

Pour les utilitaires d'installation et de configuration :

```bash
> xcode-select --install 
> open http://brew.sh
> brew install autoconf opam 
```

Pour l'interface graphique :
```bash
> brew install gtk+ --with-jasper
> brew install gtksourceview libgnomecanvas graphviz
> opam install lablgtk ocamlgraph 
```

Dépendances pour alt-ergo :
```bash
> brew install gmp
> opam install zarith
```

Frama-C et prouveur Alt-Ergo :
```bash
> opam install alt-ergo
> opam install frama-c
```

Pour vérifier l'installation, c'est dans la sous-section « Vérifier l'installation »
que les informations sont données.

## Windows

L'installation de Frama-C sous Windows passe par l'usage de Cygwin et d'une
version expérimentale d'Opam pour celui-ci. Il faut donc installer ces deux
logiciels et le compilateur Ocaml basé sur MinGW.

Les instructions d'installation se trouvent ici :

[Frama-C - Windows](https://bts.frama-c.com/dokuwiki/doku.php?id=mantis:frama-c:compiling_from_source)

Le lancement de Frama-C se fera par l'intermédiaire de cygwin.

Pour vérifier l'installation, c'est dans la sous-section « Vérifier l'installation »
que les informations sont données.

# Vérifier l'installation

Pour vérifier votre installation, nous allons utiliser ce code très simple dans un 
fichier « main.c » :

```c
/*@
  requires \valid(a) && \valid(b);
  assigns *a, *b;
  ensures *a == \old(*b);
  ensures *b == \old(*a);
*/
void swap(int* a, int* b){
  int tmp = *a;
  *a = *b;
  *b = tmp;
}

int main(){
  int a = 42;
  int b = 37;

  swap(&a, &b);

  //@ assert a == 37 && b == 42;

  return 0;
}
```

Ensuite, depuis un terminal, dans le dossier où ce fichier a été créé,
nous pouvons lancer Frama-C avec la commande suivante :

```bash
frama-c-gui -wp -rte main.c
```

Cette fenêtre devrait s'ouvrir. 

![Vérification installation 1](https://zestedesavoir.com:443/media/galleries/2584/c5a510d2-0252-4c40-a621-071a3130a641.png)

En cliquant sur ```main.c``` dans le volet latéral gauche pour le sélectionner,
nous pouvons voir le contenu du fichier ```main.c``` modifié et des pastilles 
vertes sur différentes lignes comme ceci :

![Vérification installation 2](https://zestedesavoir.com:443/media/galleries/2584/8e6fc038-29e5-479f-affd-9040454dc3aa.png)

Si c'est le cas, tant mieux, sinon il faudra d'abord vérifier que rien n'a été
oublié au cours de l'installation (par exemple : l'oubli de bibliothèques graphiques
ou encore l'oubli de l'installation d'Alt-Ergo). Si tout semble correct, divers forum
pourront vous fournir de l'aide.

[[attention]]
| L'interface graphique de Frama-C ne permet pas l'édition du code source.

[[information]]
| Pour les daltoniens, il est possible de lancer Frama-C avec un mode où les 
| pastilles de couleurs sont remplacées par des idéogrammes noirs et blancs :
| ```bash
| $ frama-c-gui -gui-theme colorblind
| ```

# (Bonus) Installation de prouveurs supplémentaires

Cette partie est purement optionnelle, rien de ce qui est ici ne sera 
complètement nécessaire pendant le tutoriel. Cependant, lorsque l'on commence à 
s'intéresser vraiment à la preuve, il est possible de toucher assez rapidement
aux limites du prouveur pré-intégré Alt-Ergo et d'avoir besoin d'outils plus 
puissants.

## Coq

Coq, développé par l'organisme de recherche Inria, est un assistant de 
preuve. C'est-à-dire que nous écrivons nous-même les preuves dans un 
langage dédié, et la plateforme se charge de vérifier (par typage) que 
cette preuve est valide. 

Pourquoi aurait-on besoin d'un tel outil ? Il se peut parfois que les 
propriétés que nous voulons prouver soient trop complexes pour un prouveur 
automatique, typiquement lorsqu'elles nécessitent des raisonnements par
induction avec des choix minutieux à chaque étape. Auquel cas, WP pourra 
générer des obligations de preuve traduites en Coq et nous laisser écrire 
la preuve en question.

Pour apprendre à utiliser Coq, 
[ce tutoriel](http://www.cis.upenn.edu/~bcpierce/sf/current/index.html) 
est très bon.

[[information]]
| Si Frama-C est installé par l'intermédiaire du gestionnaire de 
| paquets, il peut arriver que celui-ci ait directement intégré Coq.

Pour plus d'informations à propos de Coq et de son installation, voir par 
ici : [The Coq Proof Assistant](https://coq.inria.fr/).

Pour utiliser Coq lors d'une preuve dans Frama-C, il faudra le sélectionner 
par l'intermédiaire du panneau latéral à gauche, dans la partie qui concerne
WP.

![Sélectionner l'assistant de preuve Coq](https://zestedesavoir.com:443/media/galleries/2584/2210d1a1-8cc9-46bc-80d1-59db138ff2ad.png)

[[information]]
| Nous n'avons pas expérimenté cette procédure sous Windows.

## Why3

[[attention]]
| À la connaissance de l'auteur, il n'est pas possible (ou vraiment pas facile) 
| d'installer Why3 sous Windows.
| L'auteur ne saurait être tenu responsable de blessures subies
| pendant une telle opération.

Why3 est une plateforme pour la preuve déductive développée par le LRI à Orsay. 
Elle embarque en outre un langage de programmation et de spécification ainsi 
qu'un module permettant le dialogue avec une large variété de prouveurs 
automatiques et interactifs. C'est en cela qu'il peut nous intéresser. WP sera
capable de traduire ses obligations de preuve vers le langage de Why3 et 
d'utiliser ce dernier pour dialoguer avec un certain nombre de prouveurs 
automatiques.

Pour plus d'informations sur Why3 c'est [sur son site](http://why3.lri.fr/) que 
ça se passe. Si Opam est installé, Why3 est disponible par son 
intermédiaire. Sinon, il y a une procédure d'installation proposée.

Nous pouvons retrouver sur ce même site 
[la liste des prouveurs](http://why3.lri.fr/#provers) qu'il supporte.
Il est vivement conseillé d'avoir [Z3](https://github.com/Z3Prover/z3/wiki),
développé par Microsoft Research, et [CVC4](http://cvc4.cs.nyu.edu/web/),
développé par des personnes de divers organismes de recherche (New York 
University, University of Iowa, Google, CEA List). Ces deux prouveurs sont très
efficaces et relativement complémentaires.

Pour utiliser les prouveurs en question, la procédure est expliquée dans la partie
sur Coq pour la sélection d'un prouveur différent d'Alt-Ergo. À noter qu'il faudra
peut-être demander la détection des prouveurs fraîchement installé avec le 
bouton « Provers » puis « Detect Provers » dans la fenêtre qui s'ouvre.
