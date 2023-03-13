From Coq Require Import
  Strings.String ZArith.

Local Open Scope string_scope.

Definition var : Set := string.

Inductive expr : Type :=
| Var (_ : var)
| Lit (_ : Z).

Inductive stmt : Type :=
| Assign (x : var) (e : expr)    
| Seq    (a b : stmt)           
| Skip                         
.
