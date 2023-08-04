From Coq         Require Import String ZArith List.
From ASL         Require Import Semantics AST Theory.
From ASLCompiler Require Import Compiler.
From Vellvm      Require Import Semantics Syntax Utils.AListFacts. 
From ITree       Require Import ITree ITreeFacts Events.MapDefaultFacts. 

From Vellvm Require Import
Semantics Syntax TopLevel Theory Utils.PropT Handlers.Memory. 

From ITree Require Import
  ITree ITreeFacts KTree KTreeFacts Events.StateFacts Events.State.

From ExtLib Require Import
RelDec Tactics Structures.Maps.

From Coq Require Import
ZArith List String Classes.RelationClasses .


Import SemNotations.
Import ListNotations.
Import ITreeNotations.

Open Scope list_scope.
Open Scope string_scope.

Arguments next_logical_key : simpl never.
Arguments map : simpl never.

(* Just a pretty way to call a new allocated variable of name x with value i*)
Definition mem_stack_add (m:memory_stack) (x:string) (i:int32) :=
match allocate m (DTYPE_I 32%N) with
  | inr x => match write (fst x) (fst (snd x), 0%Z) (DVALUE_I32 i) with
             | inr y => y
             | inl _ => empty_memory_stack 
            end
  | inl _ => empty_memory_stack 
end.


Definition TT {A B}: A -> B -> Prop  := fun _ _ => True.
Hint Unfold TT: core.


Lemma test4 {E} :
  forall (x:global_env * unit),
  eutt eq (E:=E) (Ret x) (Ret (fst x, tt)).
Proof.
  intros.
  assert (forall (x : (global_env * unit)), x = (fst x, snd x)). {
    intros. destruct x0. reflexivity.
  }
  destruct x; destruct u.
  
  rewrite <- H at 1.  
  reflexivity.
Qed.

Lemma test3 {E} : 
  forall (t : itree E (global_env * unit)),

x <- t ;; Ret x ≈ x <- t ;; Ret (fst x, tt).
Proof.
  intros.
  setoid_rewrite <- test4.
  reflexivity.
Qed.



Lemma test2 {E} :
  forall (x:global_env * uvalue),
  eutt eq (E:=E) (Ret x) (Ret (fst x, snd x)).
Proof.
  intros.
  assert (forall (x : (global_env * uvalue)), x = (fst x, snd x)). {
    intros. destruct x0. reflexivity.
  }
  destruct x. simpl.
  reflexivity.
Qed.


Lemma test1 {E} : 
  forall (t : itree E (global_env * uvalue)),

x <- t ;; Ret x ≈ x <- t ;; Ret (fst x, snd x).
Proof.
  intros.
  setoid_rewrite <- test2.
  reflexivity.
Qed.



Lemma interp_cfg3_bind_ret_u : forall  (t : itree instr_E uvalue ) g l m,
(exists g', interp_global (interp_intrinsics t) g ≈ Ret1 g' (UVALUE_I32 (Int32.repr 1))) ->
(ℑ3 t g l m) ≈ (ℑ3 (t ;; Ret (UVALUE_I32 (Int32.repr 1))) g l m).
Proof.


  intros.
  unfold interp_cfg3.
  
  unfold interp_memory.
  unfold interp_state.
  
  assert (interp_intrinsics (t;; Ret (UVALUE_I32 (Int32.repr 1))) ≈ interp_intrinsics t;; Ret (UVALUE_I32 (Int32.repr 1))). {
    CFGTactics.go.
    setoid_rewrite interp_intrinsics_ret.
    reflexivity.
  } rewrite H0; clear H0.


  unfold interp_global in *.
  rewrite interp_state_bind .
  setoid_rewrite interp_state_ret.

  destruct H eqn:exits.
  rewrite e.
  rewrite bind_ret_.
  simpl.
reflexivity.

Qed.
 

Lemma interp_cfg3_bind_ret : forall  (t : itree instr_E unit ) g l m,
(ℑ3 t g l m) ≈ (ℑ3 (t ;; Ret tt) g l m).
Proof.
  intros.
  unfold interp_cfg3.
  
  unfold interp_memory.
  unfold interp_state.
  
  assert (interp_intrinsics (t;; Ret tt) ≈ interp_intrinsics t;; Ret tt). {
    CFGTactics.go.
    setoid_rewrite interp_intrinsics_ret.
    reflexivity.
  } rewrite H; clear H.

  unfold interp_global.
  rewrite interp_state_bind .
  setoid_rewrite interp_state_ret.
  setoid_rewrite <- test3.
  setoid_rewrite bind_ret_r.
reflexivity.

Qed.
 

Local Ltac pose_interp3_alloca m' a' A AE:=
  match goal with
  | [|-context[ℑ3  (trigger (Alloca ?t)) ?g ?l ?m]] =>
    pose proof (InterpreterCFG.interp_cfg3_alloca
                  m t g l)
      as [m' [a' [A AE]]]
  end.


(* Lemma test_two_assigns : forall g l m,
ℑ3 (⟦(IId (Name "x"), (INSTR_Op (OP_IBinop (LLVMAst.Add false false) (DTYPE_I 32%N) (EXP_Integer (0)%Z) (EXP_Integer (1)%Z))))⟧i ;; ⟦(IId (Name "x"), (INSTR_Op (OP_IBinop (LLVMAst.Add false false) (DTYPE_I 32%N) (EXP_Integer (0)%Z) (EXP_Integer (2)%Z))))⟧i) g l m
≈ Ret3 [] [] empty_memory_stack tt.
Proof.
intros.
Locate Maps.add.
assert (⟦(OP_IBinop (LLVMAst.Add false false) (DTYPE_I 32%N) (EXP_Integer (0)%Z) (EXP_Integer (1)%Z)) ⟧e3 g l m ≈ Ret3 g l m (UVALUE_I32 (Int32.repr 3%Z))). {

}
 *)


Lemma simpl_alloc : forall x g l m,
  ⟦(LLVMAst.IId (LLVMAst.Name x), LLVMAst.INSTR_Alloca (DynamicTypes.DTYPE_I 32) None None) ⟧i3 g l m ≈
  Ret3 g (FMapAList.alist_add (Name x) (UVALUE_Addr (next_logical_key m, 0%Z)) l)
    (add_to_frame (add_logical_block (next_logical_key m) (make_empty_logical_block (DTYPE_I 32)) m) (next_logical_key m)) tt.

Proof.
  intros.
  unfold denote_instr.
  cbn.
  rewrite InterpreterCFG.interp_cfg3_bind.
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
      rewrite InterpreterCFG.interp_cfg3_LW.
      unfold Maps.add. simpl. 
      reflexivity.
Qed.



From ITree Require Import Events.ExceptionFacts.
From Vellvm Require Import Theory.LocalFrame.

Lemma void_function_eq {E : Type -> Type} {X : Type} (f g : void -> itree E X) :
  f = g.
Proof.
  Locate functional_extensionality.
  apply Axioms.functional_extensionality.
  intros x.
  destruct x.
Qed.




Lemma simpl_assign_none : forall x i g l m,
lookup (Name x) l = None ->
ℑ3 (⟦(IVoid 0%Z, INSTR_Store false (DTYPE_I 32, EXP_Integer (Int32.unsigned i)) (DTYPE_Pointer, EXP_Ident (ID_Local (Name x))) None)⟧i) g l m
≈ Exception.throw tt.
Proof.
  intros.
  simpl denote_instr.
  rewrite translate_ret.
  rewrite bind_ret_.
  cbn.
  rewrite bind_ret_.
  repeat rewrite translate_trigger.
  ExpTactics.simplify_translations.
  rewrite interp_cfg3_bind.
  rewrite interp_cfg3_LR_fail.
  2: {
    apply H.
  }
  unfold raise.
  rewrite bind_bind.
  unfold print_msg.
  unfold trigger.
  rewrite bind_vis_.
  setoid_rewrite bind_ret_.

  assert ((fun x0 : void =>
   x_ <- match x0 return (itree (CallE +' PickE +' UBE +' DebugE +' FailureE) (memory_stack * (local_env * res_L1))) with
         end;;
   (let (m', p) := x_ in
    let (l', p0) := p in
    let (g', x1) := p0 in
    ℑ3
      (da <- pickUnique x1;;
       match da with
       | DVALUE_I1 _ | DVALUE_I8 _ | DVALUE_I32 _ | DVALUE_I64 _ | DVALUE_Double _ | DVALUE_Float _ =>
           vis (Store da (DVALUE_I32 (Int32.repr (Int32.unsigned i)))) (fun x3 : unit => Ret x3)
       | DVALUE_Poison => raiseUB "Store to poisoned address."
       | _ => vis (Store da (DVALUE_I32 (Int32.repr (Int32.unsigned i)))) (fun x2 : unit => Ret x2)
       end) g' l' m')) = (fun x0 : void => match x0 return (itree (CallE +' PickE +' UBE +' DebugE +' FailureE) (memory_stack * (local_env * (global_env * unit)))) with
         end)).
  {
    apply void_function_eq.
  }

  assert (vis (Exception.Throw tt)
  (fun x0 : void =>
   x_ <- match x0 return (itree (CallE +' PickE +' UBE +' DebugE +' FailureE) (memory_stack * (local_env * res_L1))) with
         end;;
   (let (m', p) := x_ in
    let (l', p0) := p in
    let (g', x1) := p0 in
    ℑ3
      (da <- pickUnique x1;;
       match da with
       | DVALUE_I1 _ | DVALUE_I8 _ | DVALUE_I32 _ | DVALUE_I64 _ | DVALUE_Double _ | DVALUE_Float _ =>
           vis (Store da (DVALUE_I32 (Int32.repr (Int32.unsigned i)))) (fun x3 : unit => Ret x3)
       | DVALUE_Poison => raiseUB "Store to poisoned address."
       | _ => vis (Store da (DVALUE_I32 (Int32.repr (Int32.unsigned i)))) (fun x2 : unit => Ret x2)
       end) g' l' m')) ≈ Exception.throw tt). { 

    unfold Exception.throw.
    rewrite H0.
    reflexivity.
  }
  rewrite H1.

  reflexivity.
Qed.



Lemma simpl_assign_2 : forall x i g l m ptr,
allocated ptr m ->
lookup (Name x) l = Some (UVALUE_Addr ptr) ->
ℑ3 (⟦(IVoid 0%Z, INSTR_Store false (DTYPE_I 32, EXP_Integer (Int32.unsigned i)) (DTYPE_Pointer, EXP_Ident (ID_Local (Name x))) None)⟧i) g l m
≈ Ret3 g l (match write m ptr (DVALUE_I32 i) with | inr x => x | _ => empty_memory_stack end) tt.
Proof.
  intros.
  simpl denote_instr.
  rewrite Int32.repr_unsigned.
  rewrite translate_ret.
  rewrite bind_ret_.
  cbn.
  rewrite bind_ret_.
  repeat rewrite translate_trigger.
  ExpTactics.simplify_translations.
  rewrite interp_cfg3_bind.
  rewrite interp_cfg3_LR.
    2: {
    Locate mapsto_lookup_alist.
    apply H0.
  }
  rewrite bind_ret_.
  cbn.
  rewrite bind_ret_.
  rewrite interp_cfg3_store .
  + reflexivity.
  + unfold write in *.
    apply allocated_get_logical_block  in H.
    destruct (get_logical_block m (fst ptr)).
    - destruct l0.
      cbn.
      destruct ptr.
      reflexivity.
    - destruct H.
      discriminate.
Qed.

Lemma simpl_assign : forall x i g l m ptr m',
lookup (Name x) l = Some (UVALUE_Addr ptr) ->
write m ptr (DVALUE_I32 (Int32.repr (Int32.unsigned i))) = inr m' ->
ℑ3 (⟦(IVoid 0%Z, INSTR_Store false (DTYPE_I 32, EXP_Integer (Int32.unsigned i)) (DTYPE_Pointer, EXP_Ident (ID_Local (Name x))) None)⟧i) g l m
≈ Ret3 g l m' tt.
Proof.
  intros.
  simpl denote_instr.
  rewrite translate_ret.
  rewrite bind_ret_.
  cbn.
  rewrite bind_ret_.
  repeat rewrite translate_trigger.
  ExpTactics.simplify_translations.
  rewrite interp_cfg3_bind.
  rewrite interp_cfg3_LR.
    2: {
    Locate mapsto_lookup_alist.
    apply H.
  }
  rewrite bind_ret_.
  cbn.
  rewrite bind_ret_.
  rewrite interp_cfg3_store .
  + reflexivity.
  + apply H0.
Qed.


Lemma two_alloc : forall g l m,
ℑ3 (⟦(IId (Name "test"), (INSTR_Alloca (DTYPE_I 32%N) None None))⟧i ;; ⟦(IId (Name "test"), (INSTR_Alloca (DTYPE_I 32%N) None None))⟧i) g l m
≈ Ret3 [] [] empty_memory_stack tt.
Proof.
  intros.
  rewrite interp_cfg3_bind.
  setoid_rewrite simpl_alloc.
  rewrite bind_ret_.
  setoid_rewrite simpl_alloc.
Admitted.


Lemma simpl_alloca_assign : forall x i g l m,
ℑ3 (⟦(IId (Name x), (INSTR_Alloca (DTYPE_I 32%N) None None))⟧i ;; ⟦(IVoid 0%Z, INSTR_Store false (DTYPE_I 32, EXP_Integer (Int32.unsigned i)) (DTYPE_Pointer, EXP_Ident (ID_Local (Name x))) None)⟧i) g l m
≈ Ret (mem_stack_add m x i, ((FMapAList.alist_add (Name x)
     (UVALUE_Addr
        (next_logical_key m, 0%Z)) l), (g, tt))).
Proof.
intros.
rewrite interp_cfg3_bind.
setoid_rewrite simpl_alloc.
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
    Locate mapsto_lookup_alist.
    rewrite mapsto_lookup. 
    replace (FMapAList.alist_add (Name x) (UVALUE_Addr (next_logical_key m, 0%Z)) l) with (add (Name x) (UVALUE_Addr (next_logical_key m, 0%Z)) l); try reflexivity.
    apply Maps.mapsto_add_eq.
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
    repeat rewrite Int32.repr_unsigned.
    reflexivity.
Qed.

Lemma intval_eq_intval : forall a b, Int32.intval a = Int32.intval b -> a = b.
Proof.
  intros.
  destruct a; destruct b.
  simpl in H.
  apply Int32.mkint_eq.
  auto.
Qed.

Lemma correct_read : forall m ptr (i:int32), match read m ptr (DTYPE_I 32) with
                    | inr (UVALUE_I32 v) => Some v
                    | _ => None
                    end = Some i <-> read m ptr (DTYPE_I 32) = inr (UVALUE_I32 i).
Proof.
  split.
  + intros.
    destruct read; try discriminate;
    destruct u; try discriminate.
    inversion H.
    f_equal.
  + intros.
    destruct read; try discriminate.
    destruct u; try discriminate.
    inversion H.
    f_equal.
Qed.

(*If I read a value in m and then I allocate a new block, the value after reading it is the same: *)
Lemma read_after_alloc_err: forall m m1 ptr ptr' e, 
  fst ptr <> (next_logical_key m) ->
  read m ptr (DTYPE_I 32) = inl e ->
  allocate m (DTYPE_I 32%N) = inr (m1, ptr') ->
  read m1 ptr (DTYPE_I 32) = inl e.
Proof.
  intros.
  unfold allocate in H1; simpl in H1.
  unfold read in H0.
  unfold read.
  inversion H1.
  rewrite get_logical_block_of_add_to_frame .
  rewrite get_logical_block_of_add_logical_frame_ineq; auto.
Qed.

(*If I read a value in m and then I allocate a new block, the value after reading it is the same: *)
Lemma read_after_alloc: forall m m1 ptr ptr' v, 
  read m ptr (DTYPE_I 32) = inr v ->
  allocate m (DTYPE_I 32%N) = inr (m1, ptr') ->
  read m1 ptr (DTYPE_I 32) = inr v.
Proof.
  intros.
  apply can_read_allocated in H as alloc_succ.
  pose proof freshly_allocated_different_blocks as diff_ptrs.
  specialize diff_ptrs with (1 := H0) (2 := alloc_succ).

  unfold allocate in H0. simpl in H0. injection H0 as m1_def.
  subst m1. unfold read.
  rewrite get_logical_block_of_add_to_frame.
  simpl.

  unfold read in H.
  simpl in H.

  assert ((fst ptr) <> (next_logical_key m)). { assert (next_logical_key m = fst ptr'). { rewrite <- H0. auto. } rewrite H1. auto. }
  rewrite get_logical_block_of_add_logical_block_neq; auto.
Qed.

Lemma read_after_alloc_write_err: forall m m1 m2 ptr ptr' e (z:int32), 
fst ptr <> (next_logical_key m) ->
read m ptr (DTYPE_I 32) = inl e ->
allocate m (DTYPE_I 32%N) = inr (m1, ptr') ->
write m1 ptr' (DVALUE_I32 z)  = inr m2 ->
read m2 ptr (DTYPE_I 32) = inl e .
Proof.
  intros.
  pose proof read_after_alloc_err.
  apply H3 with (m1:=m1) (ptr:=ptr) (ptr':=ptr') (e:=e) in H as HRead; auto.
  inversion H1.
  clear H0 H1 H3.
  subst ptr'.
  unfold write in H2.
  destruct get_logical_block; try discriminate.
  subst m1.
  destruct l.
  Arguments add_all_index : simpl never.
  Arguments serialize_dvalue : simpl never.
  simpl in H2.
  inversion H2; clear H2.
  unfold read.
  rewrite get_logical_block_of_add_logical_frame_ineq; auto.
Qed.

(*If I read a value in m and then I allocate a new block and write to it, the value after reading again in the new stack, is the same*)
Lemma read_after_alloc_write: forall m m1 m2 ptr ptr' (z:int32) v, 
read m ptr (DTYPE_I 32) = inr (UVALUE_I32 v) ->
allocate m (DTYPE_I 32%N) = inr (m1, ptr') ->
write m1 ptr' (DVALUE_I32 z)  = inr m2 ->
read m2 ptr (DTYPE_I 32) = inr (UVALUE_I32 v) .
Proof.
  intros.

  pose proof read_after_alloc.
  specialize H2 with (1 := H) (2 := H0).

  pose proof write_different_blocks.

  specialize H3 with (1 := H1) (2 := H2).

  (* First I need to demonstrate that ptr <> ptr'*)
  (* To do that, I need to demonstrate that a succesful reading implies that the ptr has been previously allocated*)
  apply can_read_allocated in H as alloc_succ.
  pose proof freshly_allocated_different_blocks as diff_ptrs.
  specialize diff_ptrs with (1 := H0) (2 := alloc_succ).

  specialize H3 with (1 := diff_ptrs).

  assert (uvalue_to_dvalue (UVALUE_I32 v) = inr (DVALUE_I32 v)); auto.

  specialize H3 with (1 := H4).

  assert (dvalue_has_dtyp (DVALUE_I32 v) (DTYPE_I 32)). { constructor. }

  specialize H3 with (1 := H5).

  assert (dvalue_has_dtyp (DVALUE_I32 z)  (DTYPE_I 32)). { constructor. }

  specialize H3 with (1 := H6).
  
  auto.
Qed.


(* write_different_blocks lemma but without the non undef requirement.*)
Lemma write_different_blocks_no_undef :
  forall m m2 p p' v v2 τ τ',
    write m p v = inr m2 ->
    read m p' τ = inr v2 ->
    fst p <> fst p' ->
    dvalue_has_dtyp v τ' ->
    read m2 p' τ = inr v2.
Proof.
  intros.
  erewrite write_untouched; eauto.
  unfold no_overlap_dtyp.
  unfold no_overlap.
  left. auto.
Qed.


(*If I read a value in m and then I allocate a new block and write to it, the value after reading again in the new stack, is the same*)
Lemma read_after_alloc_write_undef: forall m m1 m2 ptr ptr' (z:int32), 
read m ptr (DTYPE_I 32) = inr (UVALUE_Undef (DTYPE_I 32)) ->
allocate m (DTYPE_I 32%N) = inr (m1, ptr') ->
write m1 ptr' (DVALUE_I32 z)  = inr m2 ->
read m2 ptr (DTYPE_I 32) = inr (UVALUE_Undef (DTYPE_I 32)).
Proof.
  intros.

  pose proof read_after_alloc.
  specialize H2 with (1 := H) (2 := H0).

  pose proof write_different_blocks_no_undef.

  specialize H3 with (1 := H1) (2 := H2).

  (* First I need to demonstrate that ptr <> ptr'*)
  (* To do that, I need to demonstrate that a succesful reading implies that the ptr has been previously allocated*)
  apply can_read_allocated in H as alloc_succ.
  pose proof freshly_allocated_different_blocks as diff_ptrs.
  specialize diff_ptrs with (1 := H0) (2 := alloc_succ).

  specialize H3 with (1 := diff_ptrs).

  assert (dvalue_has_dtyp (DVALUE_I32 z) (DTYPE_I 32)). { constructor. }

  specialize H3 with (1 := H4).
  auto.
Qed.




Lemma same_read_mem_stack_add : 
forall m x z ptr v, read m ptr (DTYPE_I 32) = inr (UVALUE_I32 v) -> read (mem_stack_add m x z) ptr (DTYPE_I 32) = inr (UVALUE_I32 v).
Proof.
  
  intros.
    pose read_after_alloc_write.

    pose (m1 := add_to_frame (add_logical_block (next_logical_key m) (make_empty_logical_block (DTYPE_I 32)) m) (next_logical_key m)).
    pose (ptr' := ((next_logical_key m), 0%Z)).

    specialize e with (ptr' := ptr') (z := z) (ptr := ptr)  (m := m) (m1 := m1) (m2 := (mem_stack_add m x z)) (v := v) .

    assert (allocate m (DTYPE_I 32) = inr (m1, ptr')). { 
      subst m1.
      subst ptr'.
      auto.
    }

    assert (write m1 ptr' (DVALUE_I32 z) = inr (mem_stack_add m x z) ). {
      subst m1.
      subst ptr'.
      unfold mem_stack_add.
      unfold allocate.
      simpl.
      unfold write.
      repeat rewrite get_logical_block_add_to_frame .
      repeat rewrite get_logical_block_of_add_logical_block .
      simpl.
      reflexivity.
    }

    auto.
Qed.

Lemma same_read_mem_stack_add_undef : 
forall m x z ptr, read m ptr (DTYPE_I 32) = inr (UVALUE_Undef (DTYPE_I 32)) -> read (mem_stack_add m x z) ptr (DTYPE_I 32) = inr (UVALUE_Undef (DTYPE_I 32)).
Proof.
  intros.
  pose read_after_alloc_write_undef.
  pose (m1 := add_to_frame (add_logical_block (next_logical_key m) (make_empty_logical_block (DTYPE_I 32)) m) (next_logical_key m)).
    pose (ptr' := ((next_logical_key m), 0%Z)).

    specialize e with (ptr' := ptr') (z := z) (ptr := ptr)  (m := m) (m1 := m1) (m2 := (mem_stack_add m x z)) .

    assert (allocate m (DTYPE_I 32) = inr (m1, ptr')). { 
      subst m1.
      subst ptr'.
      auto.
    }

    assert (write m1 ptr' (DVALUE_I32 z) = inr (mem_stack_add m x z) ). {
      subst m1.
      subst ptr'.
      unfold mem_stack_add.
      unfold allocate.
      simpl.
      unfold write.
      repeat rewrite get_logical_block_add_to_frame .
      repeat rewrite get_logical_block_of_add_logical_block .
      simpl.
      reflexivity.
    }

    auto.
Qed.


Lemma same_read_mem_stack_add_err : 
forall m x z ptr e,
fst ptr <> (next_logical_key m) ->
read m ptr (DTYPE_I 32) = inl e -> read (mem_stack_add m x z) ptr (DTYPE_I 32) = inl e.
Proof.
  intros.
    pose proof read_after_alloc_write_err.

    pose (m1 := add_to_frame (add_logical_block (next_logical_key m) (make_empty_logical_block (DTYPE_I 32)) m) (next_logical_key m)).
    pose (ptr' := ((next_logical_key m), 0%Z)).

    specialize H1 with (ptr' := ptr') (z := z) (ptr := ptr)  (m := m) (m1 := m1) (m2 := (mem_stack_add m x z)) (e := e) .

    assert (allocate m (DTYPE_I 32) = inr (m1, ptr')). { 
      subst m1.
      subst ptr'.
      auto.
    }

    assert (write m1 ptr' (DVALUE_I32 z) = inr (mem_stack_add m x z) ). {
      subst m1.
      subst ptr'.
      unfold mem_stack_add.
      unfold allocate.
      simpl.
      unfold write.
      repeat rewrite get_logical_block_add_to_frame .
      repeat rewrite get_logical_block_of_add_logical_block .
      simpl.
      reflexivity.
    }

    auto.
Qed.



Lemma read_same_type : forall m ptr u, 
  read m ptr (DTYPE_I 32) = inr u ->
  (exists v, u = (UVALUE_I32 v)) \/ u = (UVALUE_Undef (DTYPE_I 32)).
Proof.
  intros.
  unfold read in H.
  destruct get_logical_block eqn:d; try discriminate.
  destruct l eqn:d_l; simpl in H.
  inversion H.
  unfold read_in_mem_block in H1.
  unfold deserialize_sbytes in H1.
  simpl in H1.
  unfold read_in_mem_block.
  unfold deserialize_sbytes.
  simpl. destruct all_not_sundef; auto.
  left.
  exists (Int32.repr (sbyte_list_to_Z (lookup_all_index (snd ptr) 8 bytes SUndef))).
  auto.
Qed.

Lemma same_read_mem_stack_add_eq : 
forall m x z ptr, 
fst ptr <> (next_logical_key m) ->
read m ptr (DTYPE_I 32) = read (mem_stack_add m x z) ptr (DTYPE_I 32).
Proof.
  intros.
  destruct read eqn:d_read.
  + pose proof same_read_mem_stack_add_err. symmetry. auto.
  + pose proof same_read_mem_stack_add. pose proof d_read as d_read_2.
    apply read_same_type in d_read.
    destruct u.
      all: (destruct d_read; try (destruct H1; inversion H1); try inversion H1).
    - subst.
      apply H0 with (x:=x)(z:=z) in d_read_2.
      auto.
    - pose proof same_read_mem_stack_add_undef.
      subst.
      apply H2 with (x:=x)(z:=z) in d_read_2.
      auto.
Qed.


Lemma read_result : forall m_llvm x i v, read (mem_stack_add m_llvm x i) (next_logical_key m_llvm, 0%Z) (DTYPE_I 32) = inr (UVALUE_I32 v) -> i = v.
Proof.
  Arguments add_all_index : simpl never.
  Arguments serialize_dvalue : simpl never.
  intros.
  unfold read in H.
  unfold mem_stack_add in H.
  simpl in H.
  unfold write in H.
  rewrite get_logical_block_of_add_to_frame  in H.
  rewrite get_logical_block_of_add_logical_block  in H.
  simpl in H.
  rewrite get_logical_block_of_add_logical_block  in H.
  unfold read_in_mem_block in H.
  rewrite deserialize_serialize in H; try constructor.
  + simpl in H. inversion H. reflexivity.
Qed.



(* get_logical_block_allocated but with read *)
Lemma read_allocated: forall m1 m2 τ ptr ptr_allocated,
  allocate m1 τ = inr (m2, ptr_allocated) ->
  allocated ptr m1 ->
  read m2 ptr(DTYPE_I 32) = read m1 ptr (DTYPE_I 32) .
Proof.
  Opaque add_logical_block next_logical_key.
  intros [[cm1 lm1] fs1] [[cm2 lm2] fs2] τ ptr ptr_allocated ALLOC INm1.
  unfold read.
  pose proof (allocate_correct ALLOC) as (ALLOC_FRESH & ALLOC_NEW & ALLOC_OLD).
  unfold allocate in ALLOC.
  destruct τ; inversion ALLOC.
  all :
    rewrite get_logical_block_add_to_frame;
    rewrite get_logical_block_of_add_logical_block_neq;
    [auto | apply allocated_next_key_diff; auto].
  Transparent add_logical_block next_logical_key.
Qed.

(* write_get_logical_block_neq but with read *)
Lemma write_read_neq :
      forall (m m' : memory_stack) (t : dtyp) (val : dvalue) (a a' : addr) (i i' : nat),
        write m a val = inr m' ->
        fst a' <> fst a ->
        read m a' t = read m' a' t.
    Proof.
      intros m m' t val a a' i i' WRITE NEQ.
      unfold read. 
      unfold write in WRITE.
      Tactics.break_match_hyp.
      - destruct l, a.
        cbn in WRITE; Tactics.inv WRITE.
        symmetry.
        rewrite get_logical_block_of_add_logical_frame_ineq.
        auto. simpl in NEQ. auto.
      - Tactics.inv WRITE.
    Qed.

Lemma write_alloc : forall ptr ptr' m m1 m2 v τ,
  allocated ptr m ->
  allocate m τ = inr (m1, ptr') ->
  write m1 ptr' v = inr m2 ->
  read m2 ptr (DTYPE_I 32) = read m ptr (DTYPE_I 32).
Proof.
  intros.
  apply freshly_allocated_different_blocks with (ptr1:=ptr) in H0 as diff; auto.
  apply read_allocated with (ptr := ptr) in H0; auto.
  rewrite <- H0.
  symmetry.
  apply write_read_neq with (val:=v) (a:=ptr'); auto; constructor.
Qed.

(* Lemma mem_stack_add_allocated : forall m ptr x i,
  allocated ptr m ->
  read (mem_stack_add m x i) ptr (DTYPE_I 32) = inr (UVALUE_I32 i) ->
  read m ptr (DTYPE_I 32) = inr (UVALUE_I32 i).
Proof.
  intros.
  unfold mem_stack_add in H0.
  destruct allocate eqn:des_alloc in H0; try discriminate.
  destruct write eqn:des_write in H0; try discriminate.
  rewrite <- H0; symmetry.
  destruct p; simpl in des_write.
  
  apply write_alloc with (m:=m) (v:= (DVALUE_I32 i)) (τ := DTYPE_I 32) (ptr' := a) (m2 := m0) (m1 := m1) in H; auto.
Qed. *)


Lemma get_logical_block_next_logical_key_none: forall m, get_logical_block m (next_logical_key m) = None.
Proof.
  intros.
  unfold next_logical_key.
  unfold next_logical_key_mem.
  pose proof next_logical_key_fresh.
  specialize H with  (lm:=(snd (fst m))).

  unfold get_logical_block.
  unfold get_logical_block_mem.

  destruct (Mem.lookup) eqn:LUK.
  - apply lookup_member in LUK.
    contradiction.
  - reflexivity.
Qed.

 
Lemma names_neq : forall x k,
  x <> k -> Name x <> Name k.
Proof.
  intros.
  unfold not.
  intros H'.
  inversion H'.
  contradiction.
Qed.
  


Lemma read_fresh :
  forall m v a, read m a (DTYPE_I 32) = inr (UVALUE_I32 v) -> fst a <> next_logical_key m.
Proof.
  intros.
  intros Heq.

  assert (forall m z, read m (next_logical_key m, z) (DTYPE_I 32) = inl "Attempting to read a non-allocated address"). {
      intros.
      unfold read. simpl.
      destruct get_logical_block eqn:Eqlb.
        + destruct l.
          pose proof get_logical_block_next_logical_key_none; specialize H0 with (m:=m0). rewrite H0 in Eqlb. discriminate Eqlb.
        + reflexivity.
  }

  specialize H0 with (m:=m).
  destruct a eqn:HDa.
  simpl in Heq.
  subst z.
  specialize H0 with (z:=z0).
  rewrite H in H0.
  discriminate.
Qed.



Fixpoint add_variables (vars : decs) (m:memory_stack) (l:local_env) (g:global_env) : (memory_stack * (local_env * (global_env * unit))) :=
match vars with
| nil => (m, (l, (g, tt)))
| h :: t => match h with
            | Var x =>
                let m' :=  (add_logical_block (next_logical_key m) (LBlock 8 (add_all_index (serialize_dvalue (DVALUE_I32 (Int32.repr 0))) 0 (make_empty_mem_block (DTYPE_I 32))) None)
     (add_to_frame (add_logical_block (next_logical_key m) (make_empty_logical_block (DTYPE_I 32)) m) (next_logical_key m))) in
                let l' := (FMapAList.alist_add (Name x) (UVALUE_Addr (next_logical_key m, 0%Z)) l) in
                  add_variables t m' l' g
            end
end.


Fixpoint add_variables_2 (vars : decs) (m:memory_stack) (l:local_env) (g:global_env) : (memory_stack * (local_env * (global_env * unit))) :=
match vars with
| nil => (m, (l, (g, tt)))
| h :: t => match h with
            | Var x =>
              let l' := (FMapAList.alist_add (Name x) (UVALUE_Addr (next_logical_key m, 0%Z)) l) in
              add_variables_2 t (mem_stack_add m x (Int32.repr 0%Z)) l' g
            end
end.

Fixpoint add_variables_itree_2 (vars : decs) (m:memory_stack) (l:local_env) (g:global_env) : itree (CallE +' PickE +' UBE +' DebugE +' FailureE) (memory_stack * (local_env * (global_env * unit))) :=
match vars with
| nil => Ret (m, (l, (g, tt)))
| h :: t => match h with
            | Var x =>
              let l' := (FMapAList.alist_add (Name x) (UVALUE_Addr (next_logical_key m, 0%Z)) l) in
              Tau (add_variables_itree_2 t (mem_stack_add m x (Int32.repr 0%Z)) l' g)
            end
end.



Fixpoint add_variables_itree (vars : decs) (m:memory_stack) (l:local_env) (g:global_env) : itree (CallE +' PickE +' UBE +' DebugE +' FailureE) (memory_stack * (local_env * (global_env * unit))) :=
match vars with
| nil => Ret (m, (l, (g, tt)))
| h :: t => match h with
            | Var x =>
                let m' :=   (add_logical_block (next_logical_key m) (LBlock 8 (add_all_index (serialize_dvalue (DVALUE_I32 (Int32.repr 0))) 0 (make_empty_mem_block (DTYPE_I 32))) None)
     (add_to_frame (add_logical_block (next_logical_key m) (make_empty_logical_block (DTYPE_I 32)) m) (next_logical_key m))) in
                let l' := (FMapAList.alist_add (Name x) (UVALUE_Addr (next_logical_key m, 0%Z)) l) in
                  Tau (add_variables_itree t m' l' g)
            end
end.

Lemma add_variables_itree_binds :
forall l m x t g,
add_variables_itree (Var x :: t) m l g ≈ x_ <- add_variables_itree [Var x] m l g ;; let '(m', (l', (g', tt))) := x_ in add_variables_itree t m' l' g'.
Proof.
intros.
simpl.
repeat rewrite tau_eutt.
rewrite bind_ret_.
subst.
reflexivity.
Qed.

Lemma add_variables_2_itree_binds :
forall l m x t g,
add_variables_itree_2 (Var x :: t) m l g ≈ x_ <- add_variables_itree_2 [Var x] m l g ;; let '(m', (l', (g', tt))) := x_ in add_variables_itree_2 t m' l' g'.
Proof.
intros.
simpl.
repeat rewrite tau_eutt.
rewrite bind_ret_.
subst.
reflexivity.
Qed.

Lemma add_variables_is_itree: 
forall ds m l g, 
  add_variables_itree ds m l g ≈ Ret (add_variables ds m l g).
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

Lemma add_variables_is_itree_2: 
forall ds m l g, 
  add_variables_itree_2 ds m l g ≈ Ret (add_variables_2 ds m l g).
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



