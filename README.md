**rcheck** is a type-checker for AterlierB's proof rules.
The program checks that, providing that the goal is well-typed, the instanciated sub-goals will be well-typed as well.
It also looks for unsound variable capture and variable escaping their scope.

The main advantage over the rule checker integrated in AtelierB is that **rcheck** tries to provide helpful error messages.
