From Coq         Require Import String ZArith Morphisms List.
From ASL         Require Import Semantics AST Theory.
From ASLCompiler Require Import Compiler Renv KTreeFin Fin.
From Vellvm      Require Import Semantics Syntax. 
From ITree       Require Import ITree ITreeFacts. 
From LLVMExtra   Require Import Utils.

Import SemNotations.
Import ITreeNotations.
Import ListNotations.

Open Scope string_scope.
Open Scope itree_scope.
Open Scope list_scope.

Section RAB.

  Context {A B : Type}.
  Context (RAB : A -> B -> Prop).

  
  Definition eutt_inv (r1 : (env * A)) (r2 : memory_stack * (local_env * (global_env * B))) : Prop :=
  let asl_env := fst r1 in
  let m_llvm := fst r2 in
  let l_llvm := fst (snd r2) in
  let g_llvm := fst (snd (snd r2)) in
    Renvh asl_env g_llvm l_llvm m_llvm /\ RAB (snd r1) (snd (snd (snd r2))).


  Definition bisimilar (t1 : itree (State +' CallE +' PickE +' UBE +' DebugE +' FailureE) A) (t2 : itree (instr_E) B)  :=
    forall g_llvm l_llvm m_llvm g_asl,
      Renvh g_asl g_llvm l_llvm m_llvm ->
        eutt eutt_inv
         (interp_asl t1 g_asl)
         (ℑ3 t2 g_llvm l_llvm m_llvm).

End RAB.


Global Instance eutt_bisimilar {A B}  (RAB : A -> B -> Prop):
    Proper (eutt eq ==> eutt eq ==> iff) (@bisimilar A B RAB).
  Proof.
    repeat intro.
    unfold bisimilar. split.
    - intros.
      rewrite <- H, <- H0. auto.
    - intros.
      rewrite H, H0. auto.
  Qed.


 Definition to_itree' {E A} (f : ktree_fin E 1%nat A) : itree E (fin A) := f f0.
  Lemma fold_to_itree' {E} (f : ktree_fin E 1%nat 1%nat) : f f0 = to_itree' f.
  Proof. reflexivity. Qed.

  Global Instance Proper_to_itree' {E A} :
    Proper (eq2 ==> eutt eq) (@to_itree' E A).
  Proof.
    repeat intro.
    apply H.
  Qed.


Check bisimilar.

 Lemma bisimilar_bind' {A A' B C}  (RAA' : A -> A' -> Prop) (RBC: B -> C -> Prop):
    forall (t1 : itree (State +' CallE +' PickE +' UBE +' DebugE +' FailureE) A) (t2 : itree (instr_E) A') ,
      bisimilar RAA' t1 t2 ->
      forall (k1 : A -> itree (State +' CallE +' PickE +' UBE +' DebugE +' FailureE) B) (k2 : A' -> itree (instr_E) C)
        (H: forall (a:A) (a':A'), bisimilar RBC (k1 a) (k2 a')),
        bisimilar RBC (t1 >>= k1) (t2 >>= k2).
  Proof.
    repeat intro.
    rewrite InterpreterCFG.interp_cfg3_bind .
    rewrite interp_imp_bind.
    eapply eutt_clo_bind.
    { eapply H; auto. }
    intros.
    destruct u1 as [? ?].
    destruct u2 as [? [? [? ?]]].
    unfold eutt_inv in H2.
    simpl in H2. destruct H2. subst.
    eapply H0; eauto.
  Qed.



Definition TT {A B}: A -> B -> Prop  := fun _ _ => True.
Hint Unfold TT: core.


Lemma ignore_ret_r : forall A (t1 : itree (State +' CallE +' PickE +' UBE +' DebugE +' FailureE) unit) (t2 : itree (instr_E) A) (u : uvalue), 
  bisimilar TT t1 t2 -> bisimilar TT t1 (t2;; Ret u).
Proof.

  intros.
  rewrite <- (bind_ret_r t1) at 1.
  apply bisimilar_bind' with (RAA':=TT); auto.
  intros.
  unfold bisimilar.
  intros.
  rewrite interp_asl_ret.
  rewrite InterpreterCFG.interp_cfg3_ret.
  apply eqit_Ret.
  red; simpl.
  auto.
Qed.

Lemma ignore_ret_l : forall A (t1 : itree (State +' CallE +' PickE +' UBE +' DebugE +' FailureE) unit) (t2 : itree (instr_E) A), 
  bisimilar TT t1 t2 -> bisimilar TT (t1 ;; Ret tt) t2.
Proof.

  intros.
  rewrite <- (bind_ret_r t2) at 1.
  apply bisimilar_bind' with (RAA':=TT); auto.
  intros.
  unfold bisimilar.
  intros.
  rewrite interp_asl_ret.
  rewrite InterpreterCFG.interp_cfg3_ret.
  apply eqit_Ret.
  red; simpl.
  auto.
Qed.
 

Lemma bisimilar_bind_ret : forall A (t1 : itree (State +' CallE +' PickE +' UBE +' DebugE +' FailureE) unit) (t2 : itree (instr_E) A), 
bisimilar TT (t1;; Ret tt) t2 ->
bisimilar TT t1 t2.
Proof.
  intros.
  unfold bisimilar.
  setoid_rewrite interp_asl_bind_ret.
  assumption.
Qed.


Theorem compiler_correct (s:stmt) :
  bisimilar TT (denote_asl s) (denote_code (compile s)).
Proof.

  induction s.
  + simpl.
    (* Because our expressions can only be Lit, destruct will only throw one case *)
    destruct e; simpl.
    setoid_rewrite DenotationTheory.denote_code_singleton.
    unfold gen_alloc_instr.    
    rewrite InterpreterCFG.interp_cfg3_bind.
    rewrite simpl_alloca_assign.
    repeat rewrite bind_ret_.  
    rewrite InterpreterCFG.interp_cfg3_ret.
    rewrite interp_asl_SetVar.
    red.
    apply eqit_Ret.
    unfold eutt_inv. simpl.
    split.
    - apply RenvhAssign. auto.
    - auto.
  + simpl. 
    unfold generate_cfg.
    rewrite DenotationTheory.denote_code_app_eq_itree.
    apply bisimilar_bind' with (RAA' := TT).
    - assumption.
    - intros. assumption.
  + simpl.
    rewrite DenotationTheory.denote_code_nil.
    unfold bisimilar.
    intros.
    rewrite interp_asl_ret.
    rewrite InterpreterCFG.interp_cfg3_ret.
    apply eqit_Ret.
    unfold eutt_inv.
    auto.



 (*    simpl.

  setoid_rewrite simpl_block.
 rewrite bind_bind.
  setoid_rewrite bind_ret_. 
  rewrite DenotationTheory.denote_code_app_eq_itree.
  
  apply bisimilar_bind_ret.
  apply bisimilar_bind' with (RAA' := TT) .
  - unfold bisimilar.
    apply bisimilar_bind' with (RAA' := TT) .
    --  unfold denote_cfg in IHs1.
        unfold generate_cfg in IHs1.
        simpl in IHs1.
        rewrite simpl_block in IHs1.
        rewrite bind_bind in IHs1.
        setoid_rewrite bind_ret_ in IHs1. 
        unfold bisimilar in IHs1.
        unfold bisimilar.
        intros.
        rewrite interp_cfg3_bind_ret.
        apply IHs1 in H.
        give_up.
    rewrite interp_cfg3_bind_ret.
  - 
  
 *)
 
  unfold bisimilar.
  rewrite interp_asl_bind_ret.

  rewrite <- ignore_ret_l.
  apply bisimilar_bind' with (RAA' := TT) .

  assert (bisimilar TT (denote_asl s1;; denote_asl s2) ((⟦ gen_body_code s1 ⟧c;; ⟦ gen_body_code s2 ⟧c))).
  {
  apply bisimilar_bind' with (RAA' := TT) .
  + 
    unfold denote_cfg in IHs1.
    unfold generate_cfg in IHs1.
    simpl in IHs1.
    rewrite simpl_block in IHs1.
    rewrite bind_bind in IHs1.
    setoid_rewrite bind_ret_ in IHs1. 
    apply ignore_ret_l in IHs1; auto.
    give_up.
  +
  intros.
  unfold denote_cfg in IHs2.
    unfold generate_cfg in IHs2.
    simpl in IHs2.
    rewrite simpl_block in IHs2.
    rewrite bind_bind in IHs2.
    setoid_rewrite bind_ret_ in IHs2. 

  }

  apply bisimilar_bind' with (RAA' := TT).
  - apply bisimilar_bind' with (RAA' := TT).
  

  assert (bisimilar TT (denote_asl s1;; denote_asl s2) ((⟦ nil ⟧c;; Ret (UVALUE_I32 (Int32.repr 1))))). {
  
    rewrite DenotationTheory.denote_code_nil.
    apply bisimilar_bind' with (RAA' := TT).
    + unfold bisimilar.
      intros.

    rewrite DenotationTheory.denote_code_app_eq_itree .


    eapply bisimilar_bind'.

  }

  eapply bisimilar_ret'.



  eapply bisimilar_bind'.

  unfold denote_asl; simpl.

  unfold bisimilar.
  intros.
  unfold denote_cfg; simpl.
  rewrite simpl_block.
  rewrite bind_bind.
  setoid_rewrite bind_ret_. 
  unfold denote_asl; simpl.
  induction s.
  
  + (* Assign *) 
    
    rewrite DenotationTheory.denote_code_app.
    simpl.
    (* Because our expressions can only be Lit, destruct will only throw one case *)
    destruct e; simpl.
    setoid_rewrite DenotationTheory.denote_code_singleton.
    unfold gen_alloc_instr.    
    rewrite InterpreterCFG.interp_cfg3_bind.
    rewrite simpl_alloca_assign.
    repeat rewrite bind_ret_.  
    rewrite InterpreterCFG.interp_cfg3_ret.
    rewrite interp_asl_SetVar.
    red.
    apply eqit_Ret.
    unfold eutt_inv. simpl.
    split.
    - apply RenvhAssign. auto.
    - auto.
  + (* Seq *)
    simpl.
    apply bisimilar_bind' with (RAA' := TT) (RBC := TT) .
    apply bisimilar_bind' RAA', RBC, t1, t2, k1, k2. in H.


  + (* Skip *)
    rewrite DenotationTheory.denote_code_nil.
    repeat rewrite bind_ret_.
    rewrite InterpreterCFG.interp_cfg3_ret.
    rewrite interp_asl_ret.
    red.
    apply eqit_Ret.
    unfold eutt_inv.
    auto.
Qed.