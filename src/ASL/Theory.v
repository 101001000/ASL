From Coq   Require Import List ZArith.
From ASL   Require Import Semantics.
From ITree Require Import ITree ITreeFacts Events.MapDefaultFacts Events.StateFacts. 
From Vellvm Require Import Semantics Syntax Theory.

Import SemNotations.
Import ListNotations.
Import ITreeNotations.

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

Lemma interp_asl_ret : forall (g:env) (E:Type->Type) (A:Type) x, interp_asl (E:=E) (A:=A) (Ret x) g ≈ Ret (g, x).
Proof.
  intros.
  unfold interp_asl.
  rewrite unfold_interp. simpl.
  unfold MapDefault.interp_map. cbn.
  rewrite interp_state_ret.
  reflexivity.
Qed.

