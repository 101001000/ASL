From Coq   Require Import List ZArith String.
From Lang  Require Import AST Semantics.
From ITree Require Import ITree ITreeFacts Events.MapDefaultFacts Events.StateFacts. 
From Vellvm Require Import Semantics Syntax Theory.

Import SemNotations.
Import ListNotations.
Import ITreeNotations.

Definition dec_dec : forall s1 s2 : dec, {s1 = s2} + {s1 <> s2}.
Proof.
intros.
destruct s1, s2.
destruct (string_dec x x0) as [H_eq | H_neq];
[ left; rewrite H_eq; reflexivity |
  right; intros contra; inversion contra; apply H_neq; assumption].
Qed.

Fixpoint expr_dec (e1 e2 : expr) : {e1 = e2} + {e1 <> e2}.
Proof.
  decide equality. apply Int32.eq_dec.
Defined.

Fixpoint stmt_dec (s1 s2 : stmt) : {s1 = s2} + {s1 <> s2}.
Proof.
  decide equality; apply expr_dec || apply string_dec || auto.
Defined.

Lemma test4 {E} :
  forall (x:Semantics.env * unit),
  eutt eq (E:=E) (Ret x) (Ret (fst x, tt)).
Proof.
  intros.
  assert (forall (x : (Semantics.env * unit)), x = (fst x, snd x)). {
    intros. destruct x0. reflexivity.
  }
  destruct x; destruct u.
  
  rewrite <- H at 1.  
  reflexivity.
Qed.

Lemma test3 {E} : 
  forall (t : itree E (Semantics.env * unit)),

x <- t ;; Ret x ≈ x <- t ;; Ret (fst x, tt).
Proof.
  intros.
  setoid_rewrite <- test4.
  reflexivity.
Qed.

Lemma interp_asl_bind_ret {E}: forall t env,
interp_asl (E:=E) t env ≈ interp_asl (t ;; Ret tt) env.
Proof.
  intros.
  unfold interp_asl.
  unfold MapDefault.interp_map .
  rewrite interp_bind .
  setoid_rewrite interp_ret.
  rewrite interp_state_bind.
  setoid_rewrite interp_state_ret . 
  rewrite <- bind_ret_r at 1.
  rewrite test3.
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



Lemma interp_asl_ret : forall (g:env) (E:Type->Type) (A:Type) x, interp_asl (E:=E) (A:=A) (Ret x) g ≈ Ret (g, x).
Proof.
  intros.
  unfold interp_asl.
  rewrite unfold_interp. simpl.
  unfold MapDefault.interp_map. cbn.
  rewrite interp_state_ret.
  reflexivity.
Qed.



Lemma interp_asl_bind {E} :
  forall {R S} (t: itree (State +' E) R) (k: R -> itree (State +' E)  S) e,
    interp_asl (t >>= k) e ≈
       '(e',x) <- interp_asl t e ;; interp_asl (k x) e'.
Proof.
  intros.
  unfold interp_asl.  
  rewrite interp_bind.
  unfold MapDefault.interp_map.
  rewrite interp_state_bind .
  apply eutt_eq_bind.
  intros (? & ?).
  reflexivity.
Qed.

Lemma interp_asl_SetVar : forall x g v (E:Type->Type),
    interp_asl (E:=E) (trigger (SetVar x v)) g ≈ Ret (FMapAList.alist_add x v g, tt).
Proof.
  intros.
  unfold interp_asl. simpl.
  rewrite unfold_interp. simpl. cbn. simpl.
  unfold resum, ReSum_id, id_, Id_IFun. 
  unfold cat, handle_State. cbn. unfold Cat_Handler. simpl. unfold Handler.cat. rewrite unfold_interp. simpl. unfold subevent. unfold resum, ReSum_id, id_, Id_IFun.
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