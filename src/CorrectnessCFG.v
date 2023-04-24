From Vellvm Require Import
Semantics Syntax TopLevel Theory Utils.PropT Handlers.Memory. 

From ITree Require Import
  ITree ITreeFacts KTree KTreeFacts Events.StateFacts Events.State.

From ExtLib Require Import
RelDec Tactics Structures.Maps.

From Coq Require Import
ZArith List String Classes.RelationClasses .

Import ITreeNotations.
Import ListNotations.
Import SemNotations.

Open Scope list_scope.
Open Scope string_scope.


(* The main purpose of this file, is to verify that the interpretation of a CFG of an empty function returning a 1, is in fact, 1 *)

Definition empty_block : block typ :=
    {|
      blk_id    := (Anon 0%Z);
      blk_phis  := nil;
      blk_code  := [(IId (Name "varx"), (INSTR_Alloca (TYPE_I 32%N) None None));
                               (IVoid 0%Z, (INSTR_Store false ((TYPE_I 32%N), (EXP_Integer (5)%Z)) ((TYPE_Pointer (TYPE_I 32%N)), (EXP_Ident (ID_Local (Anon 1%Z)))) None))];
      blk_term  := TERM_Ret ((TYPE_I 32%N), (EXP_Integer (1)%Z));
      blk_comments := None
    |}.

Definition empty_cfg : cfg dtyp := 
                  {|
                    init := (Anon 0%Z);
                    blks := [convert_typ [] empty_block];
                    args := nil;
                  |}.

Definition empty_denoted_cfg := denote_cfg empty_cfg.


Ltac simpl_convert_typ := 
  unfold convert_typ;
  cbn;
  rewrite typ_to_dtyp_equation.


Ltac simpl_convert_typ_block :=
  unfold convert_typ;
  unfold ConvertTyp_block;
  unfold tfmap;
  unfold TFunctor_block;
  cbn;
  repeat rewrite typ_to_dtyp_equation.

Lemma simpl_empty_block :  ⟦[{|
        blk_id := Anon 0%Z; blk_phis := []; blk_code := []; blk_term := TERM_Ret (DTYPE_I 32, EXP_Integer 1%Z); blk_comments := None
      |}] ⟧bs (Anon 0%Z, Anon 0%Z) ≈ Ret (inr (UVALUE_I32 (Int32.repr 1))).
Proof.
rewrite denote_ocfg_unfold_in.
  2:{
  simpl. destruct Eqv.eqv_dec_p.
    - reflexivity.
    - contradict n. reflexivity.
  }
  simpl.
  + rewrite denote_block_unfold_cont .
    rewrite denote_no_phis.
    rewrite bind_ret_.
    rewrite denote_code_nil.
    rewrite bind_ret_.
    cbn. setoid_rewrite bind_ret_.
    rewrite translate_ret.
    rewrite bind_ret_.
    reflexivity.
Qed.

Lemma simpl_block : forall c,
  ⟦ [{|
           blk_id := Anon 0%Z;
           blk_phis := [];
           blk_code := c;
           blk_term := TERM_Ret (DTYPE_I 32, EXP_Integer 1%Z);
           blk_comments := None
         |}] ⟧bs (Anon 0%Z, Anon 0%Z) ≈ ⟦ c ⟧c;; Ret (inr (UVALUE_I32 (Int32.repr 1))).
Proof.
intros.
rewrite denote_ocfg_unfold_in.
2:{
  simpl. destruct Eqv.eqv_dec_p.
    - reflexivity.
    - contradict n. reflexivity.
  }
  simpl.
  + rewrite denote_block_unfold_cont .
    rewrite denote_no_phis.
    rewrite bind_ret_.
    setoid_rewrite bind_ret_.
    setoid_rewrite translate_ret.
    setoid_rewrite bind_ret_.
    reflexivity.
Qed.

Local Ltac pose_interp3_alloca m' a' A AE:=
  match goal with
  | [|-context[ℑ3  (trigger (Alloca ?t)) ?g ?l ?m]] =>
    pose proof (interp_cfg3_alloca
                  m t g l)
      as [m' [a' [A AE]]]
  end.

Theorem alloca_simpl : forall x g l m, ℑ3 (denote_instr (IId (Name x), (INSTR_Alloca (DTYPE_I 32%N) None None))) g l m ≈
Ret3 g (add (Name x) (UVALUE_Addr (next_logical_key m, 0%Z)) l)
  (add_to_frame (add_logical_block (next_logical_key m) (make_empty_logical_block (DTYPE_I 32)) m) (next_logical_key m)) tt.
Proof.
  intros.
  unfold denote_instr.
  simpl.
  rewrite interp_cfg3_bind.
  pose_interp3_alloca m' a' A AE.
    + unfold non_void.
      discriminate.
    + rewrite AE.
      apply allocate_inv in A.
      simpl in A.
      destruct A. destruct H0.
      rewrite H1 in AE.
      rewrite H0, H1.
      rewrite bind_ret_.
      simpl.
      clear m' a' H H0 H1 AE.
      rewrite interp_cfg3_LW.
      reflexivity.
Qed.

Check logical_empty.
Check (snd (fst empty_memory_stack)) .
Check add 0%Z (make_empty_logical_block (DTYPE_I 32)) (snd (fst empty_memory_stack)).
Check add 0%Z (make_empty_logical_block (DTYPE_I 32)) logical_empty.

Compute (snd (fst empty_memory_stack)).

Locate err.

(* 
add 0%Z (make_empty_logical_block (DTYPE_I 32)) (snd (fst m))
(concrete_empty, add 0%Z (make_empty_logical_block (DTYPE_I 32)) logical_empty, Singleton [0%Z]) *)

(* Dado un memory stack, devolver *)

Definition mem_stack_add (m:memory_stack) (x:string) (v:Z) :=
match allocate m (DTYPE_I 32%N) with
  | inr x => match write (fst x) (snd x) (DVALUE_I32 (Int32.repr v)) with
             | inr y => y
             | inl _ => empty_memory_stack 
            end
  | inl _ => empty_memory_stack 
end.


Compute mem_stack_add empty_memory_stack "x" 5.


Lemma simpl_alloca_assign : forall x z g l m,
ℑ3 (⟦(IId (Name x), (INSTR_Alloca (DTYPE_I 32%N) None None))⟧i ;; ⟦(IVoid 0%Z, INSTR_Store false (DTYPE_I 32, EXP_Integer z) (DTYPE_Pointer, EXP_Ident (ID_Local (Name x))) None)⟧i) g l m
≈ Ret (mem_stack_add m x z, ((FMapAList.alist_add (Name x)
     (UVALUE_Addr
        (next_logical_key m, 0%Z)) l), (g, tt))).
Proof.
intros.
rewrite interp_cfg3_bind.
setoid_rewrite alloca_simpl.
rewrite bind_ret_.
simpl denote_instr.
rewrite translate_ret.
rewrite bind_ret_.
rewrite interp_cfg3_bind.
assert(H: forall g l m x, ℑ3 (concretize_or_pick (UVALUE_I32 (Int32.repr x)) True) g l m ≈ Ret (m, (l, (g, DVALUE_I32 (repr x))))).
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
  rewrite interp_cfg3_LR. 
  rewrite bind_ret_.
  2: {
    rewrite mapsto_lookup. apply mapsto_add_eq.
    Unshelve.
    2: typeclasses eauto.
  }
  cbn.
  rewrite bind_ret_.
  InstrTactics.step.
  - reflexivity.
  - unfold mem_stack_add. cbn.
    unfold allocate. simpl.
    symmetry.
    unfold write.
    rewrite get_logical_block_of_add_to_frame .
    rewrite get_logical_block_of_add_logical_block.
    simpl.
    rewrite get_logical_block_of_add_to_frame .
    rewrite get_logical_block_of_add_logical_block.
    simpl.
    reflexivity.
Qed.

(* Lemma simpl_assign : forall x z g l m,
ℑ3 (⟦(IVoid 0%Z, INSTR_Store false (DTYPE_I 32, EXP_Integer z) (DTYPE_Pointer, EXP_Ident (ID_Local (Name x))) None)⟧i) g l m
≈ Ret (empty_memory_stack, ([], ([], tt))).
Proof.
intros.
cbn.
rewrite translate_ret.
rewrite bind_ret_.
rewrite interp_cfg3_bind.
assert(H: forall g l m x, ℑ3 (concretize_or_pick (UVALUE_I32 (Int32.repr x)) True) g l m ≈ Ret (m, (l, (g, DVALUE_I32 (repr x))))).
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


Lemma simpl_alloc_assign : forall g l m x z, 
ℑ3 (⟦ [(IId (Name x), INSTR_Alloca (DTYPE_I 32) None None);
         (IVoid 0%Z, INSTR_Store false (DTYPE_I 32, EXP_Integer z) (DTYPE_Pointer, EXP_Ident (ID_Local (Name x))) None)] ⟧c;;
       Ret (UVALUE_I32 (Int32.repr 1))) g l m ≈ Ret (empty_memory_stack, ([], ([],UVALUE_I32 (repr 1)))).
Proof.
Admitted. *)

(* Theorem int_ret :
ℑ3 empty_denoted_cfg [] [] empty_memory_stack ≈ Ret (empty_memory_stack, ([], ([],UVALUE_I32 (repr 1)))).
Proof.
unfold empty_denoted_cfg.
unfold empty_cfg. cbn.
unfold empty_block.
simpl_convert_typ_block.
rewrite denote_ocfg_unfold_in.
  2:{
  simpl. destruct Eqv.eqv_dec_p.
    - reflexivity.
    - contradict n. reflexivity.
  }
  cbn.
+ repeat setoid_rewrite bind_bind.
  repeat setoid_rewrite bind_ret_.
  repeat setoid_rewrite translate_ret.
  repeat setoid_rewrite bind_ret_.
  repeat setoid_rewrite translate_trigger.
  setoid_rewrite interp_cfg3_bind.
  apply interp_cfg3_alloca .

 *)
(* 
Theorem int_ret :
ℑ3 empty_denoted_cfg [] [] empty_memory_stack ≈ Ret (empty_memory_stack, ([], ([],UVALUE_I32 (repr 1)))).
Proof.
unfold empty_denoted_cfg.
unfold empty_cfg. cbn.
unfold empty_block. simpl.
simpl_convert_typ_block.
rewrite simpl_block.
rewrite bind_ret_.
rewrite interp_cfg3_ret.
reflexivi ty.
Qed. *)