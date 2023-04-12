From Coq Require Import
  Strings.String.

(* We need to import the Vellvm int32*)
From Vellvm Require Import
  Semantics.DynamicValues.

Local Open Scope string_scope.

Inductive expr : Type :=
| Lit (_ : int32).

Inductive stmt : Type :=
| Assign (x : string) (e : expr)
| Skip.