From ASL Require Import
  Ast Denotation CompilerCFG CorrectnessCFG.

From Vellvm Require Import
  Semantics Syntax TopLevel Theory Utils.PropT. 

From ITree Require Import
  ITree ITreeFacts KTree KTreeFacts Events.StateFacts Events.MapDefaultFacts Events.StateFacts. 

From ExtLib Require Import
RelDec Tactics.

From Coq Require Import
ZArith List String Classes.RelationClasses.

Import ITreeNotations.
Import ListNotations.
Import SemNotations.

Open Scope list_scope.
Open Scope string_scope.

Lemma interp_asl_ret : forall (g:env) (E:Type->Type) x, interp_asl (E:=E) (A:=unit) (Ret x) g ≈ Ret (g, x).
Proof.
  intros; unfold ℑ3.
  unfold interp_asl.
  rewrite unfold_interp. simpl.
  unfold MapDefault.interp_map. cbn.
  rewrite interp_state_ret .
  reflexivity.
Qed.
