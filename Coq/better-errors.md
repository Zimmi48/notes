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

- Essayer de déplier la "définition" d'un type inductif conduit à un message d'erreur obscur:
````
Goal forall x, x <= x.
Fail unfold "<=".
(* The command has indeed failed with message:
Error: Unable to interpret "<=" as a reference. *)
Fail unfold le.
(* The command has indeed failed with message:
Error: Cannot coerce le to an evaluable reference. *)
````

Pourquoi ne pas plutôt écrire `Error: le is an inductive type, it cannot be coerced to an evaluable reference.`
