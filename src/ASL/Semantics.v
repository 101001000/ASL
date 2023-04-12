From Coq    Require Import String.
From Vellvm Require Import Semantics.DynamicValues.
From ITree  Require Import ITree.
From ASL    Require Import AST.
From ExtLib Require Import Structures.Monad.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

(* This is a trimmed down version of the Imp denotational semantics of the iTree tutorial *)

Variant State : Type -> Type :=
| SetVar (x : string) (v : int32) : State unit.

Section Denote.

  Context {eff : Type -> Type}.
  Context {HasState : State -< eff}.

  Fixpoint denote_expr (e : expr) : itree eff int32 :=
    match e with
    | Lit n     => ret n
    end.

  Fixpoint denote_asl (s : stmt) : itree eff unit :=
    match s with
    | Assign x e =>  v <- denote_expr e ;; trigger (SetVar x v)
    | Skip => ret tt
    end.

End Denote.