# Introduction

Les messages d'erreur de Coq pourraient être plus souvent associés à des indices sur la manière de résoudre le problème.

Penser à noter lesquels en attendant de réaliser ces améliorations.

# Liste

- Par exemple pour "Unbound and bit generalizable variable" on pourrait ajouter "You can solve this by using "Set Generalize All Variables". 

- Compiler la bibliothèque standard
````
$ coqc -beautify Znumtheory.v
Error: Cannot build module Coq.ZArith.Znumtheory.
it starts with prefix "Coq" which is reserved for the Coq library.
$ coqc -boot -beautify Znumtheory.v
````

Suggestion trouvée ici : http://coq-club.inria.narkive.com/lFC12ROu/concerning-coq-xml-output

Message d'erreur améliorable pour intégrer la suggestion.
