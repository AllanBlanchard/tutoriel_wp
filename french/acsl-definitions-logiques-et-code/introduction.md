Dans cette partie nous allons voir deux notions importantes d'ACSL :

- les définitions axiomatiques,
- le code fantôme.

Dans certaines configurations, ces deux notions sont absolument nécessaire pour
faciliter le processus de spécification et de preuve. Soit en forçant 
l'abstraction de certaines propriétés, soit en explicitant des informations qui
sont autrement implicite et plus difficile à prouver.

Le risque de ces deux notions est qu'elles peuvent rendre notre preuve inutile si
nous faisons une erreur dans leur usage. La première en nous autorisant à 
introduire des hypothèses fausses ou des définitions trop imprécises. La seconde
en nous ouvrant le risque de modifier le programme vérifié ... nous faisant 
ainsi prouver un autre programme que celui que nous voulons prouver.
