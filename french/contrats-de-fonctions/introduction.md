Il est plus que temps d'entamer les hostilités. Contrairement aux tutoriels 
sur divers langages, nous allons commencer par les fonctions. D'abord parce 
qu'il faut savoir en écrire avant d'entamer un tel tutoriel et surtout 
parce que cela permettra rapidement d'écrire quelques preuves jouables.

Au contraire, après le travail sur les fonctions, nous entamerons les notions 
les plus simples comme les affectations ou les structures conditionnelles pour 
comprendre comment fonctionne l'outil sous le capot.

Pour pouvoir prouver qu'un code est valide, il faut d'abord pouvoir spécifier 
ce que nous attendons de lui. La preuve de programme consistera donc à s'assurer 
que le code que nous avons écrit correspond bien à la spécification qui décrit
le rôle qui lui a été attribué. Comme mentionné plus tôt dans le tutoriel, la 
spécification de code pour Frama-C est faite avec le langage ACSL, celui-ci 
nous permet (mais pas seulement, comme nous le verrons dans la suite) de poser
un contrat pour chaque fonction.