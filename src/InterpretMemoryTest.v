From Vellvm Require Import
Semantics Syntax TopLevel Theory Utils.PropT. 

From ITree Require Import
  ITree ITreeFacts KTree KTreeFacts Events.StateFacts Events.State.

From ExtLib Require Import
RelDec Tactics.

From Coq Require Import
ZArith List String Classes.RelationClasses.

Import ITreeNotations.
Import ListNotations.
Import SemNotations.

Open Scope list_scope.
Open Scope string_scope.



Local Ltac pose_interp3_alloca m' a' A AE:=
  match goal with
  | [|-context[ℑ3  (trigger (Alloca ?t)) ?g ?l ?m]] =>
    pose proof (interp_cfg3_alloca
                  m t g l)
      as [m' [a' [A AE]]]
  end.

Locate add.

(* Lemma simpl_mem : (concrete_empty, add 0%Z (make_empty_logical_block (DTYPE_I 32)) logical_empty, Singleton [0%Z]) = ([], ([],[])).
 *)
Theorem alloca_test : ℑ3 (trigger (Alloca (DTYPE_I 32));;Ret (UVALUE_I32 (repr 1))) [] [] empty_memory_stack ≈
 Ret3 [] [] (concrete_empty, add 0%Z (make_empty_logical_block (DTYPE_I 32)) logical_empty, Singleton [0%Z])  (UVALUE_I32 (Int32.repr 1)).
Proof.
  rewrite interp_cfg3_bind.
  pose_interp3_alloca m' a' A AE.
    + unfold non_void.
      discriminate.
    + rewrite AE.
      cbn.
      rewrite bind_ret_.
      rewrite interp_cfg3_ret.
      apply allocate_inv in A.
      cbn in A.
      destruct A. destruct H0.
      rewrite H1 in AE.
      rewrite H0.
      reflexivity.
Qed.

Theorem alloca_simpl : forall x, ℑ3 (denote_instr (IId (Name x), (INSTR_Alloca (DTYPE_I 32%N) None None))) [] [] empty_memory_stack ≈
Ret3 [] (FMapAList.alist_add (Name x) (UVALUE_Addr (0%Z, 0%Z)) [])
  (concrete_empty, add 0%Z (make_empty_logical_block (DTYPE_I 32)) logical_empty,
  Singleton [0%Z]) tt.
Proof.
  intros.
  unfold denote_instr.
  cbn.
  rewrite interp_cfg3_bind.
  pose_interp3_alloca m' a' A AE.
    + unfold non_void.
      discriminate.
    + rewrite AE.
      apply allocate_inv in A.
      cbn in A.
      destruct A. destruct H0.
      rewrite H1 in AE.
      rewrite H0, H1.
      rewrite bind_ret_.
      cbn.
      clear m' a' H H0 H1 AE.
      rewrite interp_cfg3_LW.
      cbn.   
      reflexivity.
Qed.

Definition gen_alloca_ins (x:string) := (IId (Name x), (INSTR_Alloca (DTYPE_I 32%N) None None)).
Definition gen_store_ins (x:string) (v:int) := (IVoid 0%Z, (INSTR_Store false ((DTYPE_I 32%N), (EXP_Integer (v)%Z)) (DTYPE_Pointer, (EXP_Ident (ID_Local (Name x)))) None)).

Lemma interp_cfg3_concretize_or_pick_concrete :
  forall (uv : uvalue) (dv : dvalue) P g l m,
    is_concrete uv ->
    uvalue_to_dvalue uv = inr dv ->
    ℑ3 (concretize_or_pick uv P) g l m ≈ Ret3 g l m dv.
Proof.
  intros * CONC CONV.
  unfold concretize_or_pick.
  rewrite CONC.
  cbn.
  unfold lift_err.
  rewrite CONV.
  rewrite interp_cfg3_ret.
  reflexivity.
Qed.



Theorem x_eq_5 : ℑ3 (denote_code [(gen_alloca_ins "x") ; (gen_store_ins "x" 5%Z)]) [] [] empty_memory_stack ≈ Ret (empty_memory_stack, ((FMapAList.alist_add (Name "x") (UVALUE_Addr (0%Z, 0%Z)) []), ([], tt))).
Proof.
rewrite denote_code_cons.
rewrite interp_cfg3_bind.
unfold gen_alloca_ins.
rewrite alloca_simpl. 
rewrite bind_ret_.
rewrite denote_code_singleton.
unfold gen_store_ins.

cbn.
rewrite translate_ret.
rewrite bind_ret_.
rewrite interp_cfg3_bind.
assert(H: forall g l m, ℑ3 (concretize_or_pick (UVALUE_I32 (Int32.repr 5)) True) g l m ≈ Ret (m, (l, (g, DVALUE_I32 (repr 5))))).
  + intros.
    unfold concretize_or_pick.
    cbn.
    unfold lift_err.
    rewrite interp_cfg3_ret.
    reflexivity.
  + rewrite H; clear H.
rewrite bind_ret_.
repeat rewrite translate_trigger.
ExpTactics.simplify_translations.
rewrite interp_cfg3_bind.
assert(H: Maps.lookup (Name "x") (FMapAList.alist_add (Name "x") (UVALUE_Addr (0%Z, 0%Z)) []) = Some (UVALUE_Addr (0%Z, 0%Z))).
  - reflexivity.
  - pose proof interp_cfg3_LR.
    ExpTactics.step.
    clear H H0.
cbn.
rewrite bind_ret_.
InstrTactics.step.
  -- reflexivity.
  -- unfold write. simpl.