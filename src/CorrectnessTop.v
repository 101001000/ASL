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

Definition Renv (g_asl : Denotation.env) (g_llvm : global_env) (l_llvm : local_env) (m_llvm : memory_stack) : Prop :=
true = true.

Definition eutt_inv {R1 R2} (r1 : R1) (r2 : R2) : Prop := true = true.

Definition bisimilar (t1 : itree (ImpState +' CallE +' PickE +' UBE +' DebugE +' FailureE) unit) (t2 : itree (instr_E) uvalue)  :=
  forall g_llvm l_llvm m_llvm g_asl,
    Renv g_asl g_llvm l_llvm m_llvm ->
      eutt eutt_inv
       (interp_asl t1 g_asl)
       (ℑ3 t2 g_llvm l_llvm m_llvm).

Definition TT {A B}: A -> B -> Prop  := fun _ _ => True.
  Hint Unfold TT: core.

Lemma interp_asl_ret : forall (g:env) (E:Type->Type) x, interp_asl (E:=E) (A:=unit) (Ret x) g ≈ Ret (g, x).
Proof.
  intros; unfold ℑ3.
  unfold interp_asl.
  rewrite unfold_interp. simpl.
  unfold MapDefault.interp_map. cbn.
  rewrite interp_state_ret .
  reflexivity.
Qed.


Theorem compiler_correct (s:stmt) :
  bisimilar (denote_imp s) (denote_cfg (compile_cfg s)).
Proof.
  unfold bisimilar.
  intros.
  induction s.
  3:{
    unfold denote_cfg. simpl.
    unfold CompilerCFG.empty_block.
    rewrite simpl_block.
    rewrite bind_ret_.
    rewrite interp_cfg3_ret.
    rewrite interp_asl_ret.
    red. apply eqit_Ret.
    auto.
  }

  
