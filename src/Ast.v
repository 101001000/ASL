From Coq Require Import
  Strings.String.

Local Open Scope string_scope.

Definition var : Set := string.

Definition value : Type := nat.

Inductive expr : Type :=
| Var (_ : var)
| Lit (_ : value).

Inductive stmt : Type :=
| Assign (x : var) (e : expr)    
| Seq    (a b : stmt)           
| Skip                         
.
