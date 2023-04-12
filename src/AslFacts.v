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

Lemma interp_asl_ret : forall (g:env) (E:Type->Type) (A:Type) x, interp_asl (E:=E) (A:=A) (Ret x) g ≈ Ret (g, x).
Proof.
  intros.
  unfold interp_asl.
  rewrite unfold_interp. simpl.
  unfold MapDefault.interp_map. cbn.
  rewrite interp_state_ret .
  reflexivity.
Qed.


Lemma interp_asl_SetVar : forall x g v (E:Type->Type),
    interp_asl (E:=E) (trigger (SetVar x v)) g ≈ Ret (FMapAList.alist_add x v g, tt).
Proof.
  intros.
  unfold interp_asl. simpl.
  rewrite unfold_interp. simpl. cbn. simpl.
  unfold resum, ReSum_id, id_, Id_IFun. 
  unfold cat, handle_ImpState. cbn. unfold Cat_Handler. simpl. unfold Handler.cat. rewrite unfold_interp. simpl. unfold subevent. unfold resum, ReSum_id, id_, Id_IFun.
  setoid_rewrite interp_ret.
  unfold inl_.
  unfold Inl_sum1_Handler. 
  unfold Handler.inl_.
  unfold Handler.htrigger.
  rewrite bind_trigger.
  unfold MapDefault.interp_map. simpl.
  rewrite bind_vis_. simpl.
  rewrite interp_state_vis . simpl.
  unfold MapDefault.handle_map. simpl.
  unfold case_. simpl.
  unfold Case_sum1.
  unfold case_sum1.
  setoid_rewrite bind_tau_.
  setoid_rewrite bind_ret_.
  unfold fst. simpl.
  setoid_rewrite bind_ret_.
  setoid_rewrite interp_state_tau  .
  setoid_rewrite interp_state_tau  .
  setoid_rewrite interp_state_ret . simpl.
  repeat rewrite tau_eutt.
  reflexivity.
Qed.
