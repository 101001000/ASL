From Vellvm Require Import
  Numeric.Integers Handlers Syntax Semantics Theory.

From Coq Require Import
  String ZArith.

From ASL Require Import CorrectnessCFG.

Require Import ExtLib.Structures.Maps.

Definition trim_int_u32 (i: Z) : Z :=
  Int32.unsigned (Int32.repr i).

Lemma trim_int_u32_inrange :
  forall i, (0 <= (trim_int_u32 i) <= Int32.max_unsigned)%Z.
Proof.
  intros.
  unfold trim_int_u32.
  apply Int32.unsigned_range_2.
Qed.

(* Get the Z value of a variable name X in the memory *)
Definition get_val (g: global_env) (l: local_env) (m: memory_stack) (x: string) : option Z :=
  let addr := FMapAList.alist_find (Name x) l
  in match addr with 
    | Some (UVALUE_Addr ptr) =>
        let val := read m ptr (DTYPE_I 32%N) in 
        match val with
          | inl _ => None
          | inr v => match v with
                      | UVALUE_I32 i => Some (Int32.unsigned (i))%Z
                      | _ => None
                     end
        end
    | _ => None
  end.


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


(*If I read a value in m and then I allocate a new block and write to it, the value after reading again in the new stack, is the same*)
Lemma read_after_alloc_write: forall m m1 m2 ptr ptr' z v, 
read m ptr (DTYPE_I 32) = inr (UVALUE_I32 v) ->
allocate m (DTYPE_I 32%N) = inr (m1, ptr') ->
write m1 ptr' (DVALUE_I32 (Int32.repr z))  = inr m2 ->
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

  assert (dvalue_has_dtyp (DVALUE_I32 (Int32.repr z))  (DTYPE_I 32)). { constructor. }

  specialize H3 with (1 := H6).
  
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

  assert (write m1 ptr' (DVALUE_I32 (Int32.repr z)) = inr (mem_stack_add m x z) ). {
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


Lemma uvalue_eq_int32:
  forall (a b : int32),
    UVALUE_I32 a = UVALUE_I32 b ->
    a = b.
Proof.
  intros a b H.
  pose proof (uvalue_eq_dec (u1 := UVALUE_I32 a) (u2 := UVALUE_I32 b) ) as Hdec.
  destruct Hdec.
  - inversion e. reflexivity.
  - contradiction.
Qed.


Lemma intval_eq_intval : forall a b, Int32.intval a = Int32.intval b -> a = b.
Proof.
  intros.
  destruct a; destruct b.
  simpl in H.
  apply Int32.mkint_eq.
  auto.
Qed.


Lemma correct_int_read : forall m ptr (i:int32), match read m ptr (DTYPE_I 32) with
                    | inr (UVALUE_I32 i) => Some (Int32.intval i)
                    | _ => None
                    end = Some (Int32.intval i) <-> read m ptr (DTYPE_I 32) = inr (UVALUE_I32 i).
Proof.
  split.
  + intros.
    destruct read; try discriminate;
    destruct u eqn:Test; try discriminate.
    f_equal.
    inversion H.
    apply intval_eq_intval in H1.
    rewrite H1.
    reflexivity.
  + intros.
    destruct read; try discriminate.
    destruct u eqn:Test; try discriminate.
    inversion H.
    f_equal.
Qed.

Lemma extract_intval : forall z,
  match Int32.repr z with
  | {| Int32.intval := intval |} => intval
  end = trim_int_u32 z.
Proof.
  intros z.
  pose proof trim_int_u32_inrange.
  specialize H with (i:= z).

  destruct Int32.repr eqn:Deq.
  unfold trim_int_u32.
  unfold Int32.unsigned. auto.
  destruct (Int32.repr z) eqn:Deq2.
  simpl.
  inversion Deq.
  reflexivity.
Qed.

(* 
Lemma same_mem : forall g l m x s v z, get_val g l m x = Some v -> get_val g l (mem_stack_add m s z) x = Some v.
Proof.
  intros.
  unfold get_val.
  unfold get_val in H.
  assert (forall m s z ptr v, read m ptr (DTYPE_I 32) = inr (UVALUE_I32 v) -> read (mem_stack_add m s z) ptr (DTYPE_I 32) = inr (UVALUE_I32 v)). {
     intros.
     unfold mem_stack_add.


(* If I retrieve some value from a variable x, that value is preserved even if I add more blocks. *)
Lemma same_mem : forall g l m x s v z, get_val g l m x = Some v -> get_val g l (mem_stack_add m s z) x = Some v.
Proof.
  intros.
  unfold get_val.
  unfold get_val in H.
  assert (forall m s z ptr dv, read m ptr (DTYPE_I 32) = inr dv -> read (mem_stack_add m s z) ptr (DTYPE_I 32) = inr dv). {
    intros.
    pose proof write_different_blocks .
    unfold mem_stack_add.
    simpl.
    assert (exists m2, write (add_to_frame (add_logical_block (next_logical_key m0) (make_empty_logical_block (DTYPE_I 32)) m0) (next_logical_key m0)) (next_logical_key m0, 0%Z) (DVALUE_I32 (Int32.repr z0)) = inr m2).
    {
      assert (dvalue_has_dtyp (DVALUE_I32 (Int32.repr z0)) (DTYPE_I 32)). { constructor. }
      assert (dtyp_fits (add_to_frame (add_logical_block (next_logical_key m0) (make_empty_logical_block (DTYPE_I 32)) m0) (next_logical_key m0)) (next_logical_key m0, 0%Z) (DTYPE_I 32)). {
        unfold dtyp_fits. simpl. exists 8. simpl. rewrite get_logical_block_add_to_frame . rewrite get_logical_block_of_add_logical_block . unfold make_empty_logical_block. simpl. exists (make_empty_mem_block (DTYPE_I 32)). exists None. auto.
        assert ((8 <= 8)%Z). { reflexivity.     } auto.
      }
      pose proof write_succeeds.
      apply (H4 (add_to_frame (add_logical_block (next_logical_key m0) (make_empty_logical_block (DTYPE_I 32)) m0)
       (next_logical_key m0)) (DVALUE_I32 (Int32.repr z0)) (DTYPE_I 32) (next_logical_key m0, 0%Z)); auto.
    }
    simpl.

    assert (write (add_to_frame (add_logical_block (next_logical_key m0) (make_empty_logical_block (DTYPE_I 32)) m0) (next_logical_key m0))
      (next_logical_key m0, 0%Z) (DVALUE_I32 (Int32.repr z0)) = Some (LBlock sz bytes cid)).



    
  }

  unfold mem_stack_add.

From Coq Require Import Lia.

Lemma test : forall i, (0 <= Int32.unsigned i <= Int32.max_unsigned)%Z -> (0 <= (Int32.unsigned (i)) / 8 <= Int32.max_unsigned)%Z.
Proof.
  destruct i.
  simpl. destruct intval.
  - auto.
  - assert (forall p, (Z.pos p / 8 < Z.pos p)%Z). {
      intros.
      apply Z_div_lt.
        + lia.
        + lia.
    }
    assert (forall p, (0 <= Z.pos p / 8)%Z). {
      intros.
      apply Z_div_pos.
      + lia.
      + lia.
    }
    intros.
    specialize (H p) as H_p.
    specialize (H0 p) as H0_p.
    clear H H0 intrange.
    assert ((0 <= Z.pos p / 8 < Z.pos p)%Z). {
      auto.
    }
    lia.
  - lia.
Qed. *)

Lemma get_val_inrange : forall g l m x v,
  get_val g l m x = Some v -> (0 <= v <= Int32.max_unsigned)%Z.
Proof.
  intros.
  unfold get_val in H.
  simpl in H.
  destruct (FMapAList.alist_find (Name x) l) eqn:H1; try congruence.
  destruct u eqn:H2; try congruence.
  destruct (read m a (DTYPE_I 32)) eqn:H3; try congruence.
  destruct u0 eqn:H4; try congruence.
  inversion H.
  pose proof Int32.unsigned_range_2.
  auto.
Qed.