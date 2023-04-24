From Coq       Require Import String BinNat ZArith.
From Vellvm    Require Import Syntax Semantics Utils.AListFacts.
From ASL       Require Import Semantics.
From LLVMExtra Require Import Utils.

(* Get the Z value of a variable name X in the memory *)
Definition get_val (g: global_env) (l: local_env) (m: memory_stack) (x: string) : option int32 :=
  let addr := FMapAList.alist_find (Name x) l
  in match addr with 
    | Some (UVALUE_Addr ptr) =>
        let val := read m ptr (DTYPE_I 32%N) in 
        match val with
          | inl _ => None
          | inr v => match v with
                      | UVALUE_I32 i => Some i
                      | _ => None
                     end
        end
    | _ => None
  end.


Definition Renv (env_asl : env) (g_llvm : global_env) (l_llvm : local_env) (m_llvm : memory_stack) : Prop :=
forall k v, alist_In k env_asl v <-> get_val g_llvm l_llvm m_llvm k = Some v. 

Definition Renvh (env_asl : env) (g_llvm : global_env) (l_llvm : local_env) (m_llvm : memory_stack) : Prop :=
forall k v, (alist_In k env_asl v <-> get_val g_llvm l_llvm m_llvm k = Some v)
/\ (FMapAList.alist_find k env_asl = None <-> FMapAList.alist_find (Name k) l_llvm = None).


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


Lemma get_val_no_fresh_ptr : forall g l m x i z,
  get_val g l m x = Some i -> 
  FMapAList.alist_find (Name x) l <> Some (UVALUE_Addr (next_logical_key m, z)).
Proof.
  intros.
  unfold get_val in H.
  destruct (FMapAList.alist_find (Name x)) eqn:HDfind in H; try discriminate.
  destruct u; try discriminate.
  destruct read eqn:HDread; try discriminate.
  destruct u; try discriminate.
  clear H i.
  apply read_fresh in HDread.
  rewrite HDfind.
  intro cont.
  inversion cont.
  subst a.
  simpl in HDread.
  contradiction.
Qed.
  
Lemma next_logical_key_not_in_Renvh : forall env g l m x,
  Renvh env g l m ->
  forall z,
  FMapAList.alist_find (Name x) l <> Some (UVALUE_Addr (next_logical_key m, z)).
Proof.
  intros e g l m x HRenv z.
  unfold Renvh in HRenv.
  specialize HRenv with (k:=x).

  unfold alist_In in HRenv.
  destruct (FMapAList.alist_find x e).
  + specialize HRenv with (v := i).
    destruct HRenv.
    assert (Some i = Some i); auto.
    apply H in H1; clear H.
    apply get_val_no_fresh_ptr with (z:=z) in H1.
    auto.
  + specialize HRenv with (v := Int32.repr 0).
    destruct HRenv.
    assert (None (A:=int32) = None); auto.
    apply H0 in H1.
    rewrite H1.
    intros not.
    discriminate.
Qed.

Lemma aux: 
forall (ptr:Z*Z) m,
  (forall z, ptr <> (next_logical_key m, z)) -> fst ptr <> next_logical_key m.
Proof.
  intros.
  destruct ptr.
  unfold fst.
  intro H1.
  rewrite H1 in H.
  specialize H with (z:=z0).
  contradiction.
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

Lemma fin: forall g env l m k x i v,

Renvh env g l m ->
(get_val g l (mem_stack_add m x i) k = Some v) -> (get_val g l m k = Some v).


Proof.
  unfold get_val.
  intros.
  destruct (FMapAList.alist_find (Name k) l) eqn:HDfind; try discriminate.
  destruct u; try discriminate.
  destruct a.
  pose proof same_read_mem_stack_add_eq.
  specialize H1 with (ptr:=(z,z0)) (x:=x) (z:=i) (m:=m).
  apply next_logical_key_not_in_Renvh with (x:=k) (z:=z0) in H.
  rewrite HDfind in H.
  assert (z <> next_logical_key m). {
    intros cont.
    subst z.
    contradiction.
  }
  clear H.
  simpl in H1.
  apply H1 in H2.
  rewrite <- H2 in H0.
  auto.
Qed.


Lemma RenvhAssign :
  forall env_asl g_llvm l_llvm m_llvm x i,
  Renvh env_asl g_llvm l_llvm m_llvm -> Renvh (FMapAList.alist_add x i env_asl) g_llvm (FMapAList.alist_add (LLVMAst.Name x) (UVALUE_Addr (next_logical_key m_llvm, 0%Z)) l_llvm)
    (mem_stack_add m_llvm x i).
Proof.
  intros env_asl g_llvm l_llvm m_llvm x i H0 k v.
  unfold get_val.
  split.
  split.
  (*First, we need to ensure that every variable-value pair inside env_asl, implies it's also in llvm memory.*)
  + destruct (String.eqb_spec k x).
    (* We analyze the case where the variable added was in the Renv relationship before, so its being overwritten.*)
    - subst.
      unfold alist_In.
      intros.
      rewrite alist_find_add_eq in H.
      rewrite alist_find_add_eq .
        unfold read. simpl.
        unfold mem_stack_add.
        simpl.
        unfold write.
        rewrite get_logical_block_of_add_to_frame .
        rewrite get_logical_block_of_add_logical_block.
        Arguments add_all_index : simpl never.
        Arguments serialize_dvalue : simpl never.
        simpl get_logical_block.
        rewrite get_logical_block_of_add_logical_block.
        unfold read_in_mem_block.
        rewrite deserialize_serialize; try constructor.
        auto.
      - 
      (* We analyze the case where the variable added is new*)
        unfold alist_In.
        intros.
        (* This block can be simplified *)
        assert (FMapAList.alist_find k (FMapAList.alist_add x i env_asl) = FMapAList.alist_find k env_asl). {
          apply alist_find_neq . auto.
        }
        rewrite H1 in H.
        (* ---------------------------- *)
        unfold Renvh in H0.
        unfold alist_In in H0.
        unfold get_val in H0.
        apply H0 in H.
        rewrite alist_find_neq.
        -- destruct (FMapAList.alist_find (Name k) l_llvm); try discriminate.
           destruct u; try discriminate.
           apply correct_read.
           apply correct_read in H.
           pose proof same_read_mem_stack_add.
           auto.
        -- (* We prove that k <> x -> Name k <> Name x *)
           unfold not.
           intros H'.
           inversion H'.
           contradiction.

   + intros Mem_value.
     unfold alist_In.
     destruct (String.eqb_spec k x).
     - subst.
       rewrite alist_find_add_eq. 
       rewrite alist_find_add_eq in Mem_value.
       apply correct_read in Mem_value.
       f_equal.
       unfold Renv in H0.
       pose proof read_result.
       specialize H with (m_llvm := m_llvm) (x := x).
       apply H. auto.
      - 
        apply names_neq in n as diff_names.
        rewrite alist_find_neq; auto.
        rewrite alist_find_neq in Mem_value; auto.
        
        pose proof H0.
        unfold Renvh in H.
        apply H.

        apply fin with (k:=k) (x:=x) (i:=i) (v:=v) in H0; auto.
        
  + split.

   - intros.
     destruct (String.eqb_spec k x).
     -- subst.
        pose proof alist_find_add_eq (K:=string) (V:=int32).
        specialize H1 with (k := x) (v := i) (m:=env_asl).
        rewrite H in H1.
        discriminate.
     -- apply names_neq in n as NameNeq.
        rewrite alist_find_neq; auto.
        rewrite alist_find_neq in H; auto.
        unfold Renvh in H0.
        apply H0 in H; auto.

   - intros.
    destruct (String.eqb_spec k x).
    -- subst. 
       pose proof alist_find_add_eq (K:=raw_id) (V:=uvalue).
       specialize H1 with (k := (Name x)) (v := (UVALUE_Addr (next_logical_key m_llvm, 0%Z))) (m:=l_llvm).
       rewrite H in H1.
       discriminate.
    -- apply names_neq in n as NameNeq.
        rewrite alist_find_neq; auto.
        rewrite alist_find_neq in H; auto.
        unfold Renvh in H0.
        apply H0 in H; auto.
Qed.
