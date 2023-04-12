From Coq Require Import
  Strings.String ZArith.

Local Open Scope string_scope.

Inductive expr : Type :=
| Lit (_ : Z).

Inductive stmt : Type :=
| Assign (x : string) (e : expr)    
| Seq    (a b : stmt)           
| Skip                         
.
