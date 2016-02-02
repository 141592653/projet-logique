#     INVERSION DE MD# VIA SAT SOLVEUR - Projet Logique 2016 - Partie SAT                       

Contenu de l'archive.

## Bootstrap
Un bootstrap de projet qui contient les fonctions utilitaires pas très
intéressantes. Tout est documenté dans les *.mli et dans le code. Faites:
    `make all`
pour tout compiler et faites:
    `./hackMD -h`
pour afficher toutes les options. Une lecture rapide de la fin de main.ml peut
vous aider. Si vous créez de nouveaux fichiers sources, tout ce que vous avez
à faire et d'ajouter les .ml à la ligne 'SOURCES' du Makefile.

## Référence pour MD5 sans padding
Le binaire md5 qui vous sert de référence pour la fonction de hash MD5 sans
padding. Pour appliquer MD5 sans padding avec 1 round et 16 steps sur 512 bits
représentés en hexadecimal, faites
    `./md5 <fichier>`.
La même chose pour 4 rounds et 16 steps:
    `./md5 <fichier> -full`.
    
## Exemples
Le dossier exemples/ contient deux exemples.
1. - `0-input.hex` est l'exemple témoin constitué de 512 bits à 0.
   - `0-digest.hex` est le digest correspondant en appliquant md5 avec 1 round et
       16 étapes (sans padding).
   - `0-digest_full-md5.hex` est le digest correspondant en appliquant md5 avec 4
       rounds et 16 étapes (sans padding).

2. - `honest-text.txt` contient le texte honnête dont la représentation en hex se
       trouve dans `honest-input.hex`
   - `honest-digest.hex` est le digest que l'on obtient avec md5 et les mêmes
       paramètres que pour `0-digest.hex`.
   - `malicious-text.txt` est le genre de pre-image de `honest-digest.hex` que vous
       devez calculer.
   - `malicious-partial-input.hex` est sa représentation en hexadecimal (avec des
       0 à la fin).

## Tests
Le script test.sh lance les tests finaux (calcul de md5 partiel/complet), calcul
de pre-image et vérification et calcul de pre-image avec connaissance initiale.
Idéalement, tout les tests doivent se passer correctement dans votre projet en
forme finale.
Bien sûr, il est fortement conseillé de créer ses propres tests plus
incrémentaux et de les intégrer à la batterie de tests qui se lançent avec
l'option `-t`. Pour ajouter des tests à cette batterie, chercher `TODO` dans
`main.ml`.