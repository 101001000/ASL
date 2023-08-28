From Coq         Require Import String ZArith Morphisms List.
From ASL         Require Import Semantics AST Theory.
From ASLCompiler Require Import Compiler Renv.
From Vellvm      Require Import Semantics Syntax Utils.AListFacts. 
From ITree       Require Import ITree ITreeFacts. 
From LLVMExtra   Require Import Utils.

Import SemNotations.
Import ITreeNotations.
Import ListNotations.

Open Scope string_scope.
Open Scope itree_scope.
Open Scope list_scope.

Locate FMapAList.alist.

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


  Definition ssa_env (env_p : env) (env_ssa : env) : Prop :=
  forall k v, exists n,
  FMapAList.alist_find k env_p = Some v <-> FMapAList.alist_find n env_ssa = Some v.

Definition eutt_inv_ssa (r1 : (env * A)) (r2 : (env * B)) : Prop :=
  let env_p := fst r1 in
  let env_ssa := fst r2 in
  ssa_env env_p env_ssa /\ RAB (snd r1) (snd r2).

Definition bisimilar_ssa (t1 : itree (State +' CallE +' PickE +' UBE +' DebugE +' FailureE) A) (t2 : itree (State +' CallE +' PickE +' UBE +' DebugE +' FailureE) B) :=
  forall env_asl_0 env_asl_1,
    ssa_env env_asl_0 env_asl_1 ->
     eutt eutt_inv_ssa
      (interp_asl t1 env_asl_0)
      (interp_asl t2 env_asl_1)
  .


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


Global Instance eutt_bisimilar_ssa {A B}  (RAB : A -> B -> Prop):
    Proper (eutt eq ==> eutt eq ==> iff) (@bisimilar_ssa A B RAB).
  Proof.
    repeat intro.
    unfold bisimilar_ssa. split.
    - intros.
      rewrite <- H, <- H0. auto.
    - intros.
      rewrite H, H0. auto.
  Qed.


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

 Lemma bisimilar_ssa_bind' {A A' B C}  (RAA' : A -> A' -> Prop) (RBC: B -> C -> Prop):
    forall (t1 : itree (State +' CallE +' PickE +' UBE +' DebugE +' FailureE) A) (t2 : itree (State +' CallE +' PickE +' UBE +' DebugE +' FailureE) A') ,
      bisimilar_ssa RAA' t1 t2 ->
      forall (k1 : A -> itree (State +' CallE +' PickE +' UBE +' DebugE +' FailureE) B) (k2 : A' -> itree (State +' CallE +' PickE +' UBE +' DebugE +' FailureE) C)
        (H: forall (a:A) (a':A'), bisimilar_ssa RBC (k1 a) (k2 a')),
        bisimilar_ssa RBC (t1 >>= k1) (t2 >>= k2).
  Proof.
    repeat intro.
    repeat rewrite interp_imp_bind.
    eapply eutt_clo_bind.
    { eapply H; auto. }
    intros.
    destruct u1 as [? ?].
    destruct u2 as [? ?].
    unfold eutt_inv_ssa in H2.
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
 

Lemma ignore_ret_l2 : forall A (t1 : itree (State +' CallE +' PickE +' UBE +' DebugE +' FailureE) unit) (t2 : itree (instr_E) A), 
  bisimilar TT t1 (Ret tt;; t2) -> bisimilar TT t1 t2.
Proof.

  intros.
  rewrite (bind_ret_l ) in H.
  assumption.
Qed.

Lemma ignore_ret_l1 : forall A (t1 : itree (State +' CallE +' PickE +' UBE +' DebugE +' FailureE) unit) (t2 : itree (instr_E) A), 
  bisimilar TT (Ret tt;; t1) t2 -> bisimilar TT t1 t2.
Proof.
  intros.
  rewrite (bind_ret_l ) in H.
  assumption.
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



Check true.


Open Scope list_scope.

Fixpoint compile_decs (ds:decs) :=
match ds with
  | nil => nil
  | h :: t => match h with | DVar x => [(LLVMAst.IId (LLVMAst.Name x), LLVMAst.INSTR_Alloca (DynamicTypes.DTYPE_I 32) None None) ; (IVoid 0%Z, (INSTR_Store false ((DTYPE_I 32%N), (EXP_Integer (Int32.unsigned (Int32.repr 0%Z)))) (DTYPE_Pointer, (EXP_Ident (ID_Local (Name x)))) None)) ] ++ (compile_decs t) end
end.

Fixpoint extract_vars_p (p : stmt) : list string :=
  match p with
  | Assign x _ => [x]
  | Skip => []
  end .
 



Lemma cons_app2 : forall (A : Type) (a : A) b c  (l : list A), a :: b :: c = ([a] ++ [b]) ++ c.
Proof.
  intros. reflexivity.
Qed.

Lemma rewrite_prealloc :
forall ds g l m,
⟦ compile_decs ds ⟧c3 g l m ≈ Ret (add_variables ds m l g).
Proof.
induction ds.
+ intros.
  simpl.
  rewrite DenotationTheory.denote_code_nil.
  rewrite InterpreterCFG.interp_cfg3_ret.
  reflexivity.
+ destruct a.
intros.

assert (eutt eq (E:=(CallE +' PickE +' UBE +' DebugE +' FailureE)) (Ret (add_variables (DVar x :: ds) m l g)) (x_ <- Ret (add_variables [DVar x] m l g) ;; let '(m', (l', (g', tt))) := x_ in Ret (add_variables ds m' l' g'))). {
  setoid_rewrite <- add_variables_is_itree.
  rewrite add_variables_itree_binds.
  apply eutt_clo_bind with (UU:=eq); try reflexivity.
  intros.
  subst.
  destruct u2.
  destruct p.
  destruct p.
  destruct u.
  rewrite add_variables_is_itree.
  reflexivity.
}

  
rewrite H; clear H.

  simpl compile_decs.
  rewrite cons_app2.
  repeat setoid_rewrite DenotationTheory.denote_code_app.
  rewrite InterpreterCFG.interp_cfg3_bind.
  apply eutt_clo_bind with (UU:=eq); auto.
  - repeat setoid_rewrite DenotationTheory.denote_code_singleton.
    setoid_rewrite simpl_alloca_assign.

    unfold mem_stack_add.
    simpl.
    unfold write.
    rewrite get_logical_block_of_add_to_frame.
    rewrite get_logical_block_of_add_logical_block.
    simpl.
    reflexivity.
  - intros.
    subst.
    destruct u2.
    destruct p.
    destruct p.
    setoid_rewrite IHds.
    destruct u.
    reflexivity.
  - constructor.
Qed.


Lemma rewrite_prealloc_2 :
forall ds g l m,
⟦ compile_decs ds ⟧c3 g l m ≈ Ret (add_variables_2 ds m l g).
Proof.
induction ds.
+ intros.
  simpl.
  rewrite DenotationTheory.denote_code_nil.
  rewrite InterpreterCFG.interp_cfg3_ret.
  reflexivity.
+ destruct a.
intros.

assert (eutt eq (E:=(CallE +' PickE +' UBE +' DebugE +' FailureE)) (Ret (add_variables_2 (DVar x :: ds) m l g)) (x_ <- Ret (add_variables_2 [DVar x] m l g) ;; let '(m', (l', (g', tt))) := x_ in Ret (add_variables_2 ds m' l' g'))). {
  setoid_rewrite <- add_variables_is_itree_2.
  rewrite add_variables_2_itree_binds.
  apply eutt_clo_bind with (UU:=eq); try reflexivity.
  intros.
  subst.
  destruct u2.
  destruct p.
  destruct p.
  destruct u.
  rewrite add_variables_is_itree_2.
  reflexivity.
}

  
rewrite H; clear H.

  simpl compile_decs.
  rewrite cons_app2.
  repeat setoid_rewrite DenotationTheory.denote_code_app.
  rewrite InterpreterCFG.interp_cfg3_bind.
  apply eutt_clo_bind with (UU:=eq); auto.
  - repeat setoid_rewrite DenotationTheory.denote_code_singleton.
    setoid_rewrite simpl_alloca_assign.


    simpl.
    reflexivity.
  - intros.
    subst.
    destruct u2.
    destruct p.
    destruct p.
    setoid_rewrite IHds.
    destruct u.
    reflexivity.
  - constructor.
Qed.


Fixpoint add_variables_asl (vars : decs) (e:env) : (env * unit) :=
match vars with
| nil => (e, tt)
| h :: t => match h with
            | DVar x =>
                let e' := (FMapAList.alist_add x (Int32.repr 0%Z) e) in
                  add_variables_asl t e'
            end
end.

Fixpoint add_variables_asl_itree {E} (vars : decs) (e:env) : itree E (env * unit) :=
match vars with
| nil => Ret (e, tt)
| h :: t => match h with
            | DVar x =>
                let e' := (FMapAList.alist_add x (Int32.repr 0%Z) e) in
                  Tau (add_variables_asl_itree t e')
            end
end.


Lemma add_variables_asl_is_itree {E}: 
forall ds e, 
  add_variables_asl_itree (E:=E) ds e ≈ Ret (add_variables_asl ds e).
Proof.
induction ds.
+ simpl; reflexivity.
+ intros.
  destruct a.
  simpl.
  setoid_rewrite IHds.
  tau_steps.
reflexivity.
Qed.

Lemma add_variables_asl_itree_binds {E} :
forall e x t,
add_variables_asl_itree (E:=E) (DVar x :: t) e ≈ x_ <- add_variables_asl_itree [DVar x] e ;; let '(e',tt) := x_ in add_variables_asl_itree t e'.
Proof.
intros.
simpl.
repeat rewrite tau_eutt.
rewrite bind_ret_.
subst.
reflexivity.
Qed.


Lemma rewrite_prealloc_asl {E:Type->Type}: forall ds e,
eutt (E:=E) eq (interp_asl (denote_decs ds) e) (Ret (add_variables_asl ds e)).
Proof.
induction ds; intros.
+ simpl in *.
  rewrite interp_asl_ret.
  reflexivity.
+ destruct a.
  assert (eutt eq (E:=E) (Ret (add_variables_asl (DVar x :: ds) e)) (x_ <- Ret (add_variables_asl [DVar x] e);; (let '(e',tt) := x_ in Ret (add_variables_asl ds e')))). {
    setoid_rewrite <- add_variables_asl_is_itree.
    rewrite add_variables_asl_itree_binds.
    apply eutt_clo_bind with (UU:=eq); try reflexivity.
    intros.
    subst.
    destruct u2.
    destruct u.
    rewrite add_variables_asl_is_itree.
    reflexivity.
  }
  rewrite H; clear H.
  simpl.
  rewrite interp_asl_bind.
  apply eutt_clo_bind with (UU:=eq); auto.
  - rewrite interp_asl_SetVar.
    reflexivity.
  - intros; subst.
    destruct u2.
    destruct u.
    apply IHds.
Qed.


Lemma unfold_add_variables_2 :
forall x ds m l g,
add_variables_2 (DVar x :: ds) m l g = add_variables_2 ds (mem_stack_add m x (Int32.repr 0)) (FMapAList.alist_add (Name x) (UVALUE_Addr (next_logical_key m, 0%Z)) l) g.
Proof.
intros.
simpl.
reflexivity.
Qed.

Lemma unfold_add_variables_asl :
forall x ds e,
add_variables_asl (DVar x :: ds) e = add_variables_asl ds (FMapAList.alist_add x (Int32.repr 0) e).
Proof.
intros.
simpl.
reflexivity.
Qed.


(* Lemma Renv_presserves_assign :
forall g l m e m' i x,
(exists ptr,
Maps.lookup (Name x) l = Some (UVALUE_Addr ptr) ->
write m ptr (DVALUE_I32 (Int32.repr (Int32.unsigned i))) = inr m') ->
Renvh e g l m ->
Renvh (FMapAList.alist_add x i e) g l m'.
Proof.
intros.
unfold Renvh in *.
split.
+ split.
  - give_up.
  - give_up.
+ split.
  - give_up.
  - give_up.
Admitted. *)


Lemma Renv_preserves_after_vars_2 : forall ds g l m e g'' l'' m'' e'',
add_variables_2 ds m l g = (m'', (l'', (g'', tt))) ->
add_variables_asl ds e = (e'', tt) ->
Renvh e g l m ->
Renvh e'' g'' l'' m''.
Proof.
induction ds.
+ intros.
  simpl in *.
  injection H.
  injection H0.
  intros.
  subst.
  assumption.
+ intros.
  destruct a.
  simpl in *.
  apply IHds with (e:=(FMapAList.alist_add x (Int32.repr 0) e)) (e'':=e'') in H; auto.
  apply RenvhAssign; auto.
Qed.



Definition increasing_ptrs l m :=
forall key ptr,
FMapAList.alist_find (Name key) l = Some (UVALUE_Addr ptr) ->
(fst ptr < next_logical_key m)%Z.

(* Lemma next_logical_ley_mem_stack_add : forall m x i,
(next_logical_key m < next_logical_key (mem_stack_add m x i))%Z.
Proof.
intros.
unfold mem_stack_add.
pose proof next_logical_key_fresh .
unfold allocate. simpl.
unfold write. simpl.
rewrite get_logical_block_add_to_frame.
rewrite get_logical_block_of_add_logical_block.
simpl.
unfold next_logical_key.
unfold next_logical_key_mem.
simpl.
unfold add_logical_block.
unfold add_to_frame.
unfold add_logical_block_mem.
unfold make_empty_logical_block.
destruct m, m.
simpl.
unfold make_empty_mem_block.
simpl.
destruct f.
+ simpl.
  set (b1 := (LBlock 8
         (add_all_index (serialize_dvalue (DVALUE_I32 i)) 0
            (add 7%Z SUndef (add 6%Z SUndef (add 5%Z SUndef (add 4%Z SUndef (add 3%Z SUndef (add 2%Z SUndef (add 1%Z SUndef (add 0%Z SUndef Mem.empty))))))))) None)).
  set (b2 := LBlock 8
            (add 7%Z SUndef
               (add 6%Z SUndef (add 5%Z SUndef (add 4%Z SUndef (add 3%Z SUndef (add 2%Z SUndef (add 1%Z SUndef (add 0%Z SUndef Mem.empty))))))))
            None).
 unfold logical_next_key.
epose proof maximumBy_Z_correct.

assert (In 0%Z (List.map fst (IM.elements (elt:=logical_block) l))).
      { apply IM_key_in_elements.
        apply IM.mem_2; auto.
        give_up.
      }

  eapply H0 with (def:= (-1)%Z) in H1.
  apply Z.leb_le in H1.

  destruct (maximumBy Z.leb (-1)%Z (List.map fst (IM.elements (elt:=logical_block) l))) eqn:BLAH.
  destruct (maximumBy Z.leb (-1)%Z (List.map fst (IM.elements (elt:=logical_block) l))) eqn:BLAH.

  unfold logical_next_key.
  unfold IM.elements.
  unfold IM.Raw.elements.
  unfold IM.Raw.elements_aux.
  cbn.
  give_up.
+ simpl. *)



(* Lemma add_variables_2_incr_ptrs : forall ds m l g m' g' l',
add_variables_2 ds m l g = (m', (l', (g', tt))) ->
increasing_ptrs l m ->
increasing_ptrs l' m'.
Proof.
induction ds.
+ intros.
  simpl in *.
  injection H; intros; subst.
  assumption.
+ intros.
  destruct a.
  simpl in H. 
  apply IHds with (m:=(mem_stack_add m x (Int32.repr 0))) (l:= (FMapAList.alist_add (Name x) (UVALUE_Addr (next_logical_key m, 0%Z)) l)) (g:=g) (g':=g') (m':=m'); auto.
  unfold increasing_ptrs in *.
  intros. *)

(* Lemma add_variables_2_diff_ptrs : forall ds m l g m' g' l',
add_variables_2 ds m l g = (m', (l', (g', tt))) ->
unique_ptrs l'.
Proof.
induction ds.
+ intros.
  simpl in *.
  injection H; intros; subst.
  assumption.
+ intros.
  destruct a.
  simpl in H. 
  apply IHds with (m:=(mem_stack_add m x (Int32.repr 0))) (l:=(FMapAList.alist_add (Name x) (UVALUE_Addr (next_logical_key m, 0%Z)) l)) (g:=g) (m':=m') (g':=g') (l':=l'); auto.
  unfold unique_ptrs in *.
  split.
  - intros. 
    apply H0 with (key:=key) (key':=key'); auto.
    -- apply IHds in H2.
    give_up
Admitted.  *)


Lemma adding_stack_exists_ptr :
forall m x i m',
mem_stack_add m x i = m' ->
write ((add_to_frame (add_logical_block (next_logical_key m) (make_empty_logical_block (DTYPE_I 32)) m) (next_logical_key m))) (next_logical_key m, 0%Z) (DVALUE_I32 i) = inr m'.
Proof.
intros.
unfold mem_stack_add in H.
unfold allocate in H.
simpl in H.
unfold write in *.
simpl in *.
rewrite get_logical_block_add_to_frame in *.
rewrite get_logical_block_of_add_logical_block in *.
simpl in *.
rewrite H.
reflexivity.
Qed.

(* Lemma add_variables_x :
forall x ds m l g m' l' g',
add_variables_2 (Var x :: ds) m l g = (m', (l', (g', tt))) ->
Maps.lookup (Name x) l' = Some (UVALUE_Addr (next_logical_key m, 0%Z)) /\ write (add_to_frame (add_logical_block (next_logical_key m) (make_empty_logical_block (DTYPE_I 32)) m) (next_logical_key m)) (next_logical_key m, 0%Z) (DVALUE_I32 (Int32.repr 0)) = inr m'.
Proof.
induction ds.
+ intros.
  simpl in *.
  injection H.
  intros.
  apply adding_stack_exists_ptr in H2.
  rewrite <- H1.
  rewrite <- H2.
  rewrite alist_find_add_eq.
  auto.
+ intros.
  destruct a.

  eapply IHds.
  auto.

Admitted. *)



Definition preallocated (p:prog) (l:local_env) (g:global_env) m e : Prop :=
forall x exp,
In (Assign x exp) p ->
(exists ptr,
allocated ptr m /\
Maps.lookup (Name x) l = Some (UVALUE_Addr ptr)) /\
(exists (i:Int32.int), 
FMapAList.alist_find x e = Some i).

(* Induction is not required *)
Lemma preallocated_holds :
forall p l m g e a,
preallocated (a :: p) l g m e ->
preallocated p l g m e.
Proof.
induction p.
+ intros.
  unfold preallocated in *.
  simpl in *.
  intros; contradiction.
+ destruct a.
  - unfold preallocated in *. simpl in *.
    intros.
    apply H with (exp:=exp).
    auto.
  - unfold preallocated in *. simpl in *.
    intros.
    apply H with (exp:=exp); auto.
Qed.



Lemma allocated_holds_after_write : forall ptr ptr' m i,
allocated ptr m ->
allocated ptr' m ->
allocated ptr match write m ptr' (DVALUE_I32 i) with
                 | inl _ => empty_memory_stack
                 | inr x1 => x1
                 end.
Proof.
intros.
unfold write.
destruct (get_logical_block m (fst ptr')) eqn:EQ.
+ destruct l.
  destruct ptr'.
  simpl.
  unfold allocated.
  simpl.
  unfold allocated in H.
  simpl in H.
  unfold add_logical_block.
  unfold add_logical_block_mem.
  destruct m, m.
  rewrite member_add_preserved; auto.
+ apply allocated_get_logical_block in H0.
  destruct H0.
  rewrite H0 in EQ.
  discriminate.
Qed.
  

Lemma preallocated_holds_llvm :
forall p l g m (ptr:addr) i x e ptr,
allocated ptr m ->
preallocated p l g m e ->
preallocated p l g match write m ptr (DVALUE_I32 i) with
                   | inl _ => empty_memory_stack
                   | inr x0 => x0
                   end (FMapAList.alist_add x i e).
Proof.
unfold preallocated in *.
intros.
apply H0 in H1; try constructor.
destruct H1.
+ destruct H1.
  exists x1.
  destruct H1, H2, H3.
  apply allocated_holds_after_write with (ptr:=x1) (i:=i) in H; auto.
+ destruct H1, H1, H1.
  destruct (string_dec x x0); subst.
  - rewrite alist_find_add_eq.
    exists i.
    reflexivity.
  - rewrite alist_find_neq; auto.
Qed.


Definition well_formed (ds:decs) (p:prog) : Prop :=
forall x e,
(In (DVar x) ds <-> In (Assign x e) p) /\
((~ In (DVar x) ds) <-> (~ In (Assign x e) p)) /\
((count_occ dec_dec ds (DVar x)) < 2)%nat.



Lemma list_remove_aux : forall l (s:string),
(s, Int32.repr 0) :: FMapAList.alist_remove s l = FMapAList.alist_add s (Int32.repr 0) l.
Proof.
unfold FMapAList.alist_add.
reflexivity.
Qed.

Lemma list_remove_aux2 : forall (s:string) l i ,
(s, Int32.repr 0) :: FMapAList.alist_remove s ((s, i) :: l) = FMapAList.alist_add s (Int32.repr 0) l.
Proof.
induction l.
+ intros.
  simpl.
  rewrite RelDec.rel_dec_eq_true; auto.
  apply String.RelDec_Correct_string .
+ intros.
  unfold FMapAList.alist_add.
  destruct a as [s' i'].
  assert (H: s = s' \/ s <> s'). 
  { destruct (string_dec s s'); auto. } 
  destruct H as [H | H].
  subst.

  - simpl.
    rewrite RelDec.rel_dec_eq_true; auto.
    apply String.RelDec_Correct_string .

  - 
    simpl.
    rewrite RelDec.rel_dec_eq_true; auto.
    apply String.RelDec_Correct_string .
Qed.

  

Lemma add_variables_asl_updates : forall ds e e' x,
  add_variables_asl ds e = (e', tt) ->
  (In (DVar x) ds -> FMapAList.alist_find x e' = Some (Int32.repr 0)) /\
  (~ In (DVar x) ds -> FMapAList.alist_find x e' = FMapAList.alist_find x e).
Proof.
induction ds.
+ intros.
  simpl in *.
  split.
  - intros; contradiction.
  - intros.
    injection H.
    intros; subst.
    reflexivity.
+ split.
  - intros.
    destruct a.
    simpl in *.
    destruct (string_dec x0 x); subst.
    -- clear H0.
       specialize IHds with (e := (FMapAList.alist_add (RD_K:=String.RelDec_string) x (Int32.repr 0) e)) (e':=e') (x:=x).
       destruct (in_dec dec_dec (DVar x) ds).
       --- apply IHds; auto.
       --- rewrite alist_find_add_eq in IHds.
           apply IHds; auto.
    -- specialize IHds with (e := (FMapAList.alist_add (RD_K:=String.RelDec_string) x0 (Int32.repr 0) e)) (e':=e') (x:=x).
       destruct H0 as [H_eq | H_in].
        --- exfalso. apply n. inversion H_eq. contradiction.
        --- apply IHds; auto.      
   - intros.
     destruct a.
     simpl in *.
     destruct (string_dec x0 x); subst.
     -- assert (DVar x = DVar x \/ In (DVar x) ds). { left. reflexivity. }
        contradiction.
     -- specialize IHds with (e := (FMapAList.alist_add (RD_K:=String.RelDec_string) x0 (Int32.repr 0) e)) (e':=e') (x:=x).
        assert (~ In (DVar x) ds). {
          unfold not.
          intros.
          destruct H0; auto.

        }
        rewrite alist_find_neq in IHds; auto.
        apply IHds; auto.
Qed.
   
Require Import Lia.
     

Lemma allocated_after_allocate :
forall ptr m m' a,
allocated ptr m ->
allocate m (DTYPE_I 32) = inr (m', a) ->
allocated ptr m'.
Proof.
intros.
pose proof H0.
apply allocate_correct in H0.
inversion H0.
inversion is_allocated0.
specialize old_lu0 with (a':=ptr) (τ':=DTYPE_I 32).
apply freshly_allocated_different_blocks with (ptr1:=ptr) in H1; auto.
pose proof H.
apply allocated_can_read with (τ:=DTYPE_I 32) in H.
destruct H.
rewrite <- old_lu0 in H; auto.
apply can_read_allocated with (τ:=DTYPE_I 32) (v:=x); auto.
unfold no_overlap_dtyp.
unfold no_overlap.
auto.
Qed.

Lemma allocate_allocated : forall m m' ptr,
allocate m (DTYPE_I 32) = inr (m', ptr) ->
allocated ptr m'.
Proof.
intros.
apply allocate_correct  in H.
inversion H.
inversion is_allocated0.
assert (sizeof_dtyp (DTYPE_I 32) <> 0). simpl. lia.
apply new_lu0 in H0.
apply can_read_allocated with (DTYPE_I 32) (UVALUE_Undef (DTYPE_I 32)).
assumption.
Qed.

(* EXPLICIT VERSION WITHOUT BRACES! *)
  Lemma write_preserves_allocated :
      forall m1 m2 ptr ptr' v,
        allocated ptr' m1 ->
        write m1 ptr v = inr m2 ->
        allocated ptr' m2.
    Proof.
      intros m1 m2 ptr ptr' v ALLOC WRITE.
      unfold allocated in *.
      destruct m1 as [[cm1 lm1] f1].
      destruct m2 as [[cm2 lm2] f2].

      unfold write in WRITE.
      destruct (get_logical_block (cm1, lm1, f1) (fst ptr)) eqn:LB.
      - setoid_rewrite LB in WRITE.
        destruct l.
        destruct ptr as [ptr_b ptr_i].
        inversion WRITE; subst.
        destruct ptr' as [ptr'_b ptr'_i].
        eapply member_add_preserved; auto.
      - setoid_rewrite LB in WRITE.
        inversion WRITE.
    Qed.

Lemma allocated_after_mem_stack_add :
forall m x i ptr,
allocated ptr m ->
allocated ptr (mem_stack_add m x i).
Proof.
intros.
unfold mem_stack_add.
destruct allocate eqn:ALLOC.
+ pose proof allocate_succeeds.
  specialize H0 with (m1:=m) (τ:=(DTYPE_I 32)).
  assert (non_void (DTYPE_I 32)). 
  discriminate.
  apply H0 in H1.
  destruct H1, H1.
  rewrite H1 in ALLOC.
  discriminate.
+ destruct p.
  apply allocated_after_allocate with (m':=m0) (a:=a) in H; auto.
  simpl in *.
  apply allocate_allocated in ALLOC.
  destruct write eqn:WRITE.
  - unfold write in WRITE.
    simpl in WRITE.
    apply allocated_get_logical_block in ALLOC.
    destruct ALLOC.
    rewrite H0 in WRITE.
    destruct x0.
    discriminate.
  - apply write_preserves_allocated with (m1:=m0) (ptr:=(fst a, 0%Z)) (v:=DVALUE_I32 i); auto.
Qed.

Lemma add_variables_hold_ptr : forall ds m l g m' g' l' ptr,
allocated ptr m ->
add_variables_2 ds m l g = (m', (l', (g' tt))) ->
allocated ptr m'.
Proof.
induction ds; intros.
+ simpl in *.
  inversion H0.
  subst.
  assumption.
+ destruct a.
  simpl in H0.
  apply IHds with (g:=g) (g':=g') (m:=(mem_stack_add m x (Int32.repr 0))) (l:=(FMapAList.alist_add (Name x) (UVALUE_Addr (next_logical_key m, 0%Z)) l)) (l':=l'); auto.
  apply allocated_after_mem_stack_add.
  assumption.
Qed.

(* Lemma add_variables_hold_l : forall ds m l g m' g' l' x,
In (Var x) ds ->
add_variables_2 ds m l g = (m', (l', (g', tt))) ->
exists ptr,
FMapAList.alist_find (Name x) l' = Some ptr.
Proof.
induction ds; intros.
+ simpl in *.
  contradiction.
+ destruct a.
  destruct (string_dec x x0); subst.
  - clear H.
    simpl in H0.
  
  

  simpl in H0.
  apply IHds with (g:=g) (g':=g') (m:=(mem_stack_add m x (Int32.repr 0))) (l:=(FMapAList.alist_add (Name x) (UVALUE_Addr (next_logical_key m, 0%Z)) l)) (l':=l'); auto.
  apply allocated_after_mem_stack_add.
  assumption.
Qed. *) 

Lemma read_mem_stack_add : forall m x i,
read (mem_stack_add m x i) (next_logical_key m, 0%Z) (DTYPE_I 32)  = inr (UVALUE_I32 i).
Proof.
intros.
unfold mem_stack_add.
simpl.
unfold write.
rewrite get_logical_block_of_add_to_frame.
rewrite get_logical_block_of_add_logical_block.
simpl.
unfold read.
rewrite get_logical_block_of_add_logical_block.
simpl.
unfold read_in_mem_block.
rewrite deserialize_serialize; auto; try constructor.
Qed.



Lemma mem_stack_add_allocated : forall m x i,
allocated (next_logical_key m, 0%Z) (mem_stack_add m x i).
Proof.
intros.
pose proof read_mem_stack_add.
specialize H with m x i.
apply can_read_allocated in H.
assumption.
Qed.

Lemma add_variables_2_updates_ptr : forall ds m l g x m' g' l',
  add_variables_2 ds m l g = (m', (l', (g' tt))) ->
  (In (DVar x) ds -> exists ptr, FMapAList.alist_find (Name x) l' = Some (UVALUE_Addr ptr) /\ allocated ptr m') /\
  (~In (DVar x) ds -> FMapAList.alist_find (Name x) l' = FMapAList.alist_find (Name x) l).
Proof.
induction ds.
+ intros.
  split.
  - intros.
    simpl in *.
    contradiction.
  - intros.
    simpl in *.
    injection H.
    intros; subst.
    reflexivity.
    
+ split.
   - intros.
    destruct a.
    simpl in *.
    destruct (string_dec x0 x); subst.
    -- clear H0.
       specialize IHds with (l := (FMapAList.alist_add (RD_K:=eq_dec_raw_id) (Name x)(UVALUE_Addr (next_logical_key m, 0%Z))  l)) (l':=l') (x:=x) (m:=(mem_stack_add m x (Int32.repr 0))) (g:=g) (g':=g') (m':=m').
       destruct (in_dec dec_dec (DVar x) ds).
       --- apply IHds; auto.
       --- rewrite alist_find_add_eq in IHds.
           exists ((next_logical_key m, 0%Z)).
           assert (allocated (next_logical_key m, 0%Z) (mem_stack_add m x (Int32.repr 0))). apply mem_stack_add_allocated.
           apply add_variables_hold_ptr with (g:=g) (g':=g') (ds:=ds) (l':=l') (m':=m') (l:=(FMapAList.alist_add (Name x) (UVALUE_Addr (next_logical_key m, 0%Z)) l)) in H0; auto.
           split; auto.
           apply IHds; auto.
    -- specialize IHds with (l := (FMapAList.alist_add (RD_K:=eq_dec_raw_id) (Name x0) (UVALUE_Addr (next_logical_key m, 0%Z)) l)) (l':=l') (x:=x) (m:=(mem_stack_add m x0 (Int32.repr 0))) (g:=g) (m':=m') (g':=g').
       destruct H0 as [H_eq | H_in].
        --- exfalso. apply n. inversion H_eq. contradiction.
        --- apply IHds; auto.      
   - intros.
     destruct a.
     simpl in *.
     destruct (string_dec x0 x); subst.
     -- assert (DVar x = DVar x \/ In (DVar x) ds). { left. reflexivity. }
        contradiction.
     -- specialize IHds with (l := (FMapAList.alist_add (RD_K:=eq_dec_raw_id) (Name x0) (UVALUE_Addr (next_logical_key m, 0%Z)) l)) (l':=l') (x:=x) (m:=(mem_stack_add m x0 (Int32.repr 0))) (g:=g) (m':=m') (g':=g').
        assert (~ In (DVar x) ds). {
          unfold not.
          intros.
          destruct H0; auto.

        }
        rewrite alist_find_neq in IHds; auto.
        apply IHds; auto.
        apply names_neq; auto.
Qed.


(* Lemma add_variables_2_updates_ptr_2 : forall ds m l g x m' g' l',
  add_variables_2 ds m l g = (m', (l', (g' tt))) ->
  (In (Var x) ds -> (exists ptr m'', FMapAList.alist_find (Name x) l' = Some (UVALUE_Addr ptr) /\ write m'' (ptr) (DVALUE_I32 (Int32.repr 0)) = inr m')) /\
  (~In (Var x) ds -> FMapAList.alist_find (Name x) l' = FMapAList.alist_find (Name x) l).
Proof.
induction ds.
+ intros.
  split.
  - intros.
    simpl in *.
    contradiction.
  - intros.
    simpl in *.
    injection H.
    intros; subst.
    reflexivity.
    
+ split.
   - intros.
    destruct a.
    simpl in *.
    destruct (string_dec x0 x); subst.
    -- clear H0.
       specialize IHds with (l := (FMapAList.alist_add (RD_K:=eq_dec_raw_id) (Name x)(UVALUE_Addr (next_logical_key m, 0%Z))  l)) (l':=l') (x:=x) (m:=(mem_stack_add m x (Int32.repr 0))) (g:=g) (g':=g') (m':=m').
       destruct (in_dec dec_dec (Var x) ds).
       --- apply IHds; auto.
       --- rewrite alist_find_add_eq in IHds.
           exists (next_logical_key m, 0%Z).
      
           exists (add_to_frame (add_logical_block (next_logical_key m) (make_empty_logical_block (DTYPE_I 32%N)) m) (next_logical_key m)).
           pose proof write_succeeds .
    
           give_up.
    -- specialize IHds with (l := (FMapAList.alist_add (RD_K:=eq_dec_raw_id) (Name x0) (UVALUE_Addr (next_logical_key m, 0%Z)) l)) (l':=l') (x:=x) (m:=(mem_stack_add m x0 (Int32.repr 0))) (g:=g) (m':=m') (g':=g').
       destruct H0 as [H_eq | H_in].
        --- exfalso. apply n. inversion H_eq. contradiction.
        --- apply IHds; auto.      
   - intros.
     destruct a.
     simpl in *.
     destruct (string_dec x0 x); subst.
     -- assert (Var x = Var x \/ In (Var x) ds). { left. reflexivity. }
        contradiction.
     -- specialize IHds with (l := (FMapAList.alist_add (RD_K:=eq_dec_raw_id) (Name x0) (UVALUE_Addr (next_logical_key m, 0%Z)) l)) (l':=l') (x:=x) (m:=(mem_stack_add m x0 (Int32.repr 0))) (g:=g) (m':=m') (g':=g').
        assert (~ In (Var x) ds). {
          unfold not.
          intros.
          destruct H0; auto.

        }
        rewrite alist_find_neq in IHds; auto.
        apply IHds; auto.
        apply names_neq; auto.
Admitted. *)

Lemma add_variables_asl_find_add : forall ds e e' x,
add_variables_asl ds (FMapAList.alist_add x (Int32.repr 0) e) = (e', tt) ->
FMapAList.alist_find x e' = Some (Int32.repr 0).
Proof.
intros.
apply add_variables_asl_updates with (x:=x) in H.
destruct (in_dec dec_dec (DVar x) ds).
+ apply H; auto.
+ rewrite alist_find_add_eq in H.
  apply H; auto.
Qed.


Lemma add_variables_asl_some_i : forall x ds e e',
In (DVar x) ds ->
add_variables_asl ds e = (e', tt) ->
exists i, FMapAList.alist_find x e' = Some i.
Proof.
induction ds; intros.
+ simpl in H. contradiction.
+ destruct a.
  destruct (string_dec x x0); subst.
  - intros.
    simpl in H0.
    apply add_variables_asl_find_add in H0.
    exists (Int32.repr 0).
    assumption.
  - simpl in H.
    destruct H.
    assert (DVar x0 <> DVar x). {
      unfold not.
      intros H'.
      inversion H'.
      symmetry in H2.
      contradiction.
    }
    -- contradiction.
    -- simpl in H0.
       apply IHds with (e:=(FMapAList.alist_add x0 (Int32.repr 0) e)); auto.
Qed.

(* Lemma unfold_add_variables_2_2 : forall m l g m' l' g' x ds,
add_variables_2 ds m l g = (m', (l', (g', tt))) ->
add_variables_2 (Var x :: ds) m l g = ((mem_stack_add m' x (Int32.repr 0)), ((FMapAList.alist_add (Name x) (UVALUE_Addr (next_logical_key m, 0%Z)) l'), (g', tt))).
Proof.
induction ds; intros.
+ simpl in *.
  inversion H.
  subst.
  reflexivity.
+ destruct a.
 *)
(* 
Lemma add_variables_2_keep_alloc :
forall m l g m' l' g' ptr ds,
allocated ptr m ->
add_variables_2 ds m l g = (m', (l', (g', tt))) ->
allocated ptr m'.
Proof.
induction ds; intros.
+ simpl in *.
  inversion H0.
  subst.
  assumption.
+ destruct a.
  destruct ds.
  - simpl in *. give_up.
  - 
  unfold add_variables_2 in IHds.
  simpl in H0.




  destruct ds as [| d ds'].
  - simpl in *. give_up.
  - destruct d. simpl in H0.
  unfold add_variables_2 in H0.
  destruct vars in H0.
  apply IHds; auto.
  
Admitted.
 *) 

(* Lemma unfold_add_variables_2_2 : forall ds m x l g m' l' g',
add_variables_2 ds (mem_stack_add m x (Int32.repr 0))
      (FMapAList.alist_add (Name x) (UVALUE_Addr (next_logical_key m, 0%Z)) l) g = (m', (l', (g', tt))) ->
add_variables_2 ds m l g = ((mem_stack_add m' x (Int32.repr 0)), ((FMapAList.alist_add (Name x) (UVALUE_Addr (next_logical_key m, 0%Z)) l'), (g', tt))).
Proof.
induction ds; intros.
+ simpl in *.
  inversion H.
  give_up.
+ destruct a. give_up.
Admitted. *)



(* 
Lemma asdasd : forall ds m m' g g' l l' x,
add_variables_2 ds (mem_stack_add m x (Int32.repr 0))(FMapAList.alist_add (Name x) (UVALUE_Addr (next_logical_key m, 0%Z)) l) g = (m', (l', (g', tt))) ->
exists ptr : addr, allocated ptr m' /\ Maps.lookup (Name x) l' = Some (UVALUE_Addr ptr).
Proof.
induction ds; intros.
+ simpl in H.
  inversion H; intros; subst.
  unfold Maps.lookup.
  simpl.
  rewrite alist_find_add_eq.
  exists (next_logical_key m, 0%Z).
  split.
  - apply mem_stack_add_allocated.
  - reflexivity.
+ destruct a.
  apply IHds in H.


  specialize IHds with (m:=(mem_stack_add m x0 (Int32.repr 0))) (g:=g) (g':=g') (x:=x) (l:= (FMapAList.alist_add (RD_K:=eq_dec_raw_id) (Name x) (UVALUE_Addr (next_logical_key m, 0%Z)) l)).
  apply IHds.
  - (* destruct H0.
    destruct (string_dec x x0); subst.
    -- exists x1. assumption.
    --


  eapply IHds.

  (* apply IHds with (g:=g) (g':=g') . *)
  unfold mem_stack_add in H.

  specialize IHds with (m:=(mem_stack_add m x0 (Int32.repr 0))) (g:=g) (g':=g') (x:=x) (l:= (FMapAList.alist_add (RD_K:=eq_dec_raw_id) (Name x) (UVALUE_Addr (next_logical_key m, 0%Z)) l)).
  apply IHds. *)
 
Admitted. *)



Lemma add_variables_2_all_find : forall x ds m l g m' l' g',
In (DVar x) ds ->
add_variables_2 ds m l g = (m', (l', (g', tt))) ->
exists ptr,
allocated ptr m' /\ Maps.lookup (Name x) l' = Some (UVALUE_Addr ptr).
Proof.
induction ds; intros.
+ simpl in H. contradiction.
+ destruct a.
  destruct (string_dec x x0); subst.
  - pose proof add_variables_2_updates_ptr.
    apply H1 with (x:=x0) in H0.
    apply H0 in H.
    destruct H, H.
    exists x.
    split; auto.
  - simpl in H0.
    simpl in H.
    destruct H.
    assert (DVar x0 <> DVar x). {
      unfold not.
      intros H'.
      inversion H'.
      symmetry in H2.
      contradiction.
    }
    -- contradiction.
    -- apply IHds with (m:=(mem_stack_add m x0 (Int32.repr 0))) (l:=(FMapAList.alist_add (Name x0) (UVALUE_Addr (next_logical_key m, 0%Z)) l)) (g:=g) (g':=g'); auto.
Qed.


(* Lemma add_variables_2_ptr :
forall ds m l g m' l' g' x,
In (Var x) ds ->
add_variables_2 ds m l g = (m', (l', (g', tt))) ->
exists ptr m'',
Maps.lookup (Name x) l' = Some (UVALUE_Addr ptr) /\
write m'' ptr (DVALUE_I32 (Int32.repr 0)) = inr m'.
Proof.
induction ds.
+ intros.
  simpl in *.
  contradiction.
+ intros.
  destruct a.
  simpl in H0.
  rewrite unfold_add_variables_2 in H0.
  apply IHds with (m:=(mem_stack_add m x0 (Int32.repr 0))) (l:=(FMapAList.alist_add (Name x0) (UVALUE_Addr (next_logical_key m, 0%Z)) l)) (g:=g) (g':=g'); auto.
Admitted. *)


Lemma add_variables_prealloc : forall l m g e ds p l' m' g' e',
well_formed ds p ->
add_variables_2 ds m l g = (m', (l', (g', tt))) ->
add_variables_asl ds e = (e', tt) ->
preallocated p l' g' m' e'.
Proof.
unfold preallocated.
intros.
unfold well_formed in H.
specialize H with (x:=x) (e:=exp).
destruct H.
apply H in H2.
split.
+ apply add_variables_2_all_find with (ds:=ds) (m:=m) (l:=l) (g:=g) (g':=g'); auto.
+ apply add_variables_asl_some_i with (ds:=ds) (e:=e); auto.
Qed.


 Lemma denote_exp_i32 :forall t g l m,
      ⟦ EXP_Integer (Int32.intval t) at (DTYPE_I 32) ⟧e3 g l m
        ≈
        Ret (m, (l, (g, UVALUE_I32 t))).
  Proof.
Admitted.



Lemma simpl_ident : forall g l m n i,
ℑ3 (⟦ (IId (Raw (n)%Z), INSTR_Op (EXP_Integer (Int32.unsigned i))) ⟧i) g l m ≈ Ret3 g (FMapAList.alist_add (Raw n) (UVALUE_I32 i) l) m tt.
Admitted.

Lemma simpl_assign_3 : forall x i g l m ptr n,
allocated ptr m ->
Maps.lookup (Name x) l = Some (UVALUE_Addr ptr) ->
ℑ3 (⟦(IVoid 0%Z, INSTR_Store false (DTYPE_I 32, EXP_Ident (ID_Local (Raw n))) (DTYPE_Pointer, EXP_Ident (ID_Local (Name x))) None)⟧i) g (FMapAList.alist_add (Raw n) (UVALUE_I32 i) l) m
≈ Ret3 g (FMapAList.alist_add (Raw n) (UVALUE_I32 i) l) (match write m ptr (DVALUE_I32 i) with | inr x => x | _ => empty_memory_stack end) tt.
Admitted.

(* Definition non_mod (g g' : global_env) (l l' : local_env) (m m' : memory_stack) : Prop := 
g = g' /\
m = m' /\
forall x v, FMapAList.alist_find (Name x) l = Some v <-> FMapAList.alist_find (Name x) l = Some v.

Lemma compile_non_mod : forall p g l m g0 l0 m0 g1 l1 m1,
⟦ compile_aux p 0 ⟧c3 g l m ≈ Ret3 g0 l0 m0 tt ->
⟦ compile_aux p 1 ⟧c3 g l m ≈ Ret3 g1 l1 m1 tt ->
non_mod g0 g1 l0 l1 m0 m1.
Proof.
induction p; intros.
+ give_up.
+ simpl in *.
  simpl in *.

  - 
Admitted. *)

Lemma bind_ret1 {RR} {E}: forall v p,
eutt RR (E:=E) (x_ <- Ret1 v tt;; (let (e', _) := x_ in interp_asl p e')) (interp_asl (A:=unit) p v).
Proof.
intros.
rewrite bind_ret_.
red.
Admitted.

(* Lemma test2 {A} : forall p t1 n g l i m,
eutt (eutt_inv (A:=A) TT) t1 (⟦ compile_aux p (n + 1) ⟧c3 g (FMapAList.alist_add (Raw n) (UVALUE_I32 i) l) m) ->
eutt (eutt_inv (A:=A) TT) t1 (⟦ compile_aux p (n + 1) ⟧c3 g (FMapAList.alist_add (Raw (n + 1)%Z) (UVALUE_I32 i) l) m).
Proof.
induction p; intros.
+ simpl in *.
  give_up.
+ 
 *)

Lemma test : forall p e g l m n,
eutt (eutt_inv TT) (interp_asl (denote_prog p) e) (⟦ compile_aux p n ⟧c3 g l m) ->
eutt (eutt_inv TT) (interp_asl (denote_prog p) e) (⟦ compile_aux p (n + 1)⟧c3 g l m).
Proof.
induction p; intros.
+ simpl in *; auto.
+ simpl in *.
  destruct a.
  - destruct e0; simpl in *; rewrite interp_asl_bind.
    -- rewrite bind_ret_.
       rewrite interp_asl_SetVar.
       rewrite bind_ret_.
       repeat setoid_rewrite DenotationTheory.denote_code_cons.
       rewrite InterpreterCFG.interp_cfg3_bind.
       rewrite simpl_ident.
       rewrite bind_ret_.
       rewrite InterpreterCFG.interp_cfg3_bind.
       assert (exists ptr, allocated ptr m /\ Maps.lookup (Name x) l = Some (UVALUE_Addr ptr)). give_up.
       destruct H0 as [ptr].
       destruct H0.



       rewrite simpl_assign_3 with (ptr:=ptr); auto.
       --- rewrite bind_ret_.
           apply IHp.
           assert (eutt eq (E:=(CallE +' PickE +' UBE +' DebugE +' FailureE)) (interp_asl (denote_prog p) (FMapAList.alist_add x i e)) (interp_asl ((v <- Ret i;; trigger (SetVar x v));; denote_prog p) e)). {
            rewrite bind_ret_.
            rewrite interp_asl_bind.
            rewrite interp_asl_SetVar.
            rewrite bind_ret_.
            reflexivity.
            }
           clear H2.
           assert (⟦ (IId (Raw n), INSTR_Op (EXP_Integer (Int32.unsigned i)))
               :: (IVoid 0%Z,
                  INSTR_Store false (DTYPE_I 32, EXP_Ident (ID_Local (Raw n)))
                    (DTYPE_Pointer, EXP_Ident (ID_Local (Name x))) None) :: 
                  compile_aux p (n + 1) ⟧c3 g l m ≈ (⟦ compile_aux p (n + 1) ⟧c3 g (FMapAList.alist_add (Raw n) (UVALUE_I32 i) l)
           match write m ptr (DVALUE_I32 i) with
           | inl _ => empty_memory_stack
           | inr x0 => x0
           end)). {
              repeat setoid_rewrite DenotationTheory.denote_code_cons.
               rewrite InterpreterCFG.interp_cfg3_bind.
               rewrite simpl_ident.
               rewrite bind_ret_.
               rewrite InterpreterCFG.interp_cfg3_bind.
               rewrite simpl_assign_3 with (ptr:=ptr); auto.
               rewrite bind_ret_.
                reflexivity.
           }
           clear H2.
           
           assert (eutt (eutt_inv TT) (interp_asl (denote_prog p) (FMapAList.alist_add x i e))
                (⟦ compile_aux p (n + 1) ⟧c3 g (FMapAList.alist_add (Raw n) (UVALUE_I32 i) l)
                   match write m ptr (DVALUE_I32 i) with
                   | inl _ => empty_memory_stack
                   | inr x0 => x0
                   end)). give_up.
          give_up.
    -- give_up.
       
    
  - simpl in *.
    rewrite interp_asl_bind.
    rewrite interp_asl_ret.
    rewrite bind_ret_.
    apply IHp.
    give_up.
Admitted.

Lemma compile_all_n : forall p e g l m n,
eutt (eutt_inv TT) (interp_asl (denote_prog p) e) (⟦ compile_aux p n ⟧c3 g l m) ->
eutt (eutt_inv TT) (interp_asl (denote_prog p) e) (⟦ compile_aux p (n + 1)⟧c3 g l m).
Admitted.

Theorem compiler_correct_prealloc :
forall (p:prog) l g m e n,
preallocated p l g m e ->
Renvh e g l m ->
eutt (eutt_inv TT) (interp_asl (denote_prog p) e) (⟦ compile_aux p n ⟧c3 g l m).
Proof.
induction p.
+ intros.
  simpl.
  rewrite DenotationTheory.denote_code_nil.
  red.
  intros.
  rewrite interp_asl_ret.
  rewrite InterpreterCFG.interp_cfg3_ret.
  apply eutt_Ret.
  unfold eutt_inv.
  simpl.
  auto.
+ destruct a.
  - intros.
    simpl in *.
    pose proof H as PREALLOC.
    destruct e.
    -- simpl.
      setoid_rewrite bind_ret_.
      rewrite interp_asl_bind.
      setoid_rewrite interp_asl_SetVar.
      setoid_rewrite bind_ret_.
      rewrite DenotationTheory.denote_code_cons.
      rewrite InterpreterCFG.interp_cfg3_bind.
      assert (⟦ EXP_Integer (Int32.unsigned i) ⟧e3 g l m ≈ Ret3 g l m (UVALUE_I32 i)). give_up.
      eapply InstrLemmas.denote_instr_op with (i:=(Raw n)) in H1; auto.
      rewrite H1; clear H1.
      rewrite bind_ret_.
      simpl in *.
      rewrite DenotationTheory.denote_code_cons.
      rewrite InterpreterCFG.interp_cfg3_bind.
      unfold preallocated in H.
      specialize H with (x:=x) (exp:=(Lit i)).
    destruct (in_dec stmt_dec (Assign x (Lit i)) (Assign x (Lit i) :: p)).
        --- apply H in i0.
           destruct i0.
           destruct H1 as [ptr].
           destruct H1.
           setoid_rewrite simpl_assign_3 with (ptr:=ptr); auto.
           rewrite bind_ret_.
           apply compile_all_n.
           apply IHp.
           ---- apply preallocated_holds in PREALLOC.
               apply preallocated_holds_llvm; auto.
                give_up.
           ---- destruct H2.
               apply Renv_holds with (i0:=x0); auto.
        -- simpl in n.
           destruct n. 
           auto.
          give_up.
    --



intros.
    pose proof H as PREALLOC.
    destruct e.
    simpl in *.
    setoid_rewrite bind_ret_.
    rewrite interp_asl_bind.
    setoid_rewrite interp_asl_SetVar.
    setoid_rewrite bind_ret_.
    rewrite DenotationTheory.denote_code_cons.
    rewrite InterpreterCFG.interp_cfg3_bind.

    unfold preallocated in H.
    specialize H with (x:=x) (exp:=(Lit i)).

    destruct (in_dec stmt_dec (Assign x (Lit i)) (Assign x (Lit i) :: p)).
    -- apply H in i0.
       destruct i0.
       destruct H1 as [ptr].
       destruct H1.
       setoid_rewrite simpl_assign_2 with (ptr:=ptr); auto.
       rewrite bind_ret_.
       apply IHp.
       --- apply preallocated_holds in PREALLOC.
           apply preallocated_holds_llvm; auto.
       --- destruct H2.
           apply Renv_holds with (i0:=x0); auto.
    -- simpl in n.
       destruct n. 
       auto.
    -- simpl in *.
  - simpl in *.
    intros.
    rewrite bind_ret_.
    apply IHp; auto.
    unfold preallocated in H.
    unfold preallocated.
    intros.
    simpl in *.
    apply H with (exp:expr); auto.
Admitted.


(* 
Theorem compiler_correct_prealloc :
forall (p:prog) l g m e,
preallocated p l g m e ->
Renvh e g l m ->
eutt (eutt_inv TT) (interp_asl (denote_prog p) e) (⟦ compile p ⟧c3 g l m).
Proof.

induction p.
+ intros.
  simpl.
  rewrite DenotationTheory.denote_code_nil.
  red.
  intros.
  rewrite interp_asl_ret.
  rewrite InterpreterCFG.interp_cfg3_ret.
  apply eutt_Ret.
  unfold eutt_inv.
  simpl.
  auto.
+ destruct a.
  - intros.
    pose proof H as PREALLOC.
    destruct e.
    simpl in *.
    setoid_rewrite bind_ret_.
    rewrite interp_asl_bind.
    setoid_rewrite interp_asl_SetVar.
    setoid_rewrite bind_ret_.
    rewrite DenotationTheory.denote_code_cons.
    rewrite InterpreterCFG.interp_cfg3_bind.

    unfold preallocated in H.
    specialize H with (x:=x) (exp:=(Lit i)).

    destruct (in_dec stmt_dec (Assign x (Lit i)) (Assign x (Lit i) :: p)).
    -- apply H in i0.
       destruct i0 as [ptr].
       destruct H1, H2.
       setoid_rewrite simpl_assign_2 with (ptr:=ptr); auto.
       rewrite bind_ret_.
       apply IHp.
       --- apply preallocated_holds in PREALLOC.
           apply preallocated_holds_llvm; auto.
       --- destruct H3.
           apply Renv_holds with (i0:=x0); auto.
    -- simpl in n.
       destruct n. 
       auto.
  - simpl in *.
    intros.
    rewrite bind_ret_.
    apply IHp; auto.
    unfold preallocated in H.
    unfold preallocated.
    intros.
    simpl in *.
    apply H with (exp:expr); auto.
Qed. *)




Theorem compiler_correct (ds:decs) (p:prog) :
  well_formed ds p ->
  bisimilar TT (denote_decs ds ;; denote_prog p) (denote_code ((compile_decs ds) ++ (compile p))).
Proof.
  unfold bisimilar.
  intros.

  rewrite DenotationTheory.denote_code_app_eq_itree.
  
  setoid_rewrite InterpreterCFG.interp_cfg3_bind.
  setoid_rewrite rewrite_prealloc_2.
  rewrite bind_ret_.

  destruct (add_variables_2 ds m_llvm l_llvm g_llvm) as [m'] eqn:Eqn1.
  destruct p0 as [l'].
  destruct p0 as [g'].
  destruct u.

  rewrite interp_asl_bind.
  rewrite rewrite_prealloc_asl.
  rewrite bind_ret_.
  destruct (add_variables_asl ds g_asl) as [e'] eqn:Eqn2.
  destruct u.

  assert (HPrealloc : preallocated p l' g' m' e').
  apply (add_variables_prealloc l_llvm m_llvm g_llvm g_asl ds p l' m' g' e' H Eqn1 Eqn2).
  apply Renv_preserves_after_vars_2 with (e:=g_asl) (e'':=e')  in Eqn1; auto.
  apply compiler_correct_prealloc; auto.
Qed.

