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


(* The main purpose of this file, is to verify that the interpretation of a CFG of an empty function returning a 1, is in fact, 1 *)

Definition empty_block : block dtyp :=
    {|
      blk_id    := (Anon 0%Z);
      blk_phis  := nil;
      blk_code  := nil;
      blk_term  := TERM_Ret ((DTYPE_I 32%N), (EXP_Integer (1)%Z));
      blk_comments := None
    |}.

Definition empty_cfg : cfg dtyp := 
                  {|
                    init := (Anon 0%Z);
                    blks := [empty_block];
                    args := nil;
                  |}.

Definition empty_denoted_cfg := denote_cfg empty_cfg.

Lemma simpl_block :  ⟦[{|
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

Theorem int_ret :
ℑ3 empty_denoted_cfg [] [] empty_memory_stack ≈ Ret (empty_memory_stack, ([], ([],UVALUE_I32 (repr 1)))).
Proof.
unfold empty_denoted_cfg.
unfold empty_cfg. cbn.
unfold empty_block. simpl.
rewrite simpl_block.
rewrite bind_ret_.
rewrite interp_cfg3_ret.
reflexivity.
Qed.