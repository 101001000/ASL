From Coq       Require Import String BinNat ZArith.
From Vellvm    Require Import Syntax Semantics Utils.AListFacts.
From ASL       Require Import Semantics.
From LLVMExtra Require Import Utils.

Require Import Lia.

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

Definition unique_ptrs l :=
forall key key' ptr ptr',
key <> key' ->
FMapAList.alist_find (Name key) l = Some (UVALUE_Addr ptr) ->
FMapAList.alist_find (Name key') l = Some (UVALUE_Addr ptr') ->
fst ptr <> fst ptr'.

Definition no_next_key l m :=
forall key ptr,
FMapAList.alist_find (Name key) l = Some (UVALUE_Addr ptr) ->
(fst ptr < next_logical_key m)%Z.


Definition Renvh (env_asl : env) (g_llvm : global_env) (l_llvm : local_env) (m_llvm : memory_stack) : Prop :=
forall k v, (alist_In k env_asl v <-> get_val g_llvm l_llvm m_llvm k = Some v)
/\ (FMapAList.alist_find k env_asl = None <-> FMapAList.alist_find (Name k) l_llvm = None)
/\ unique_ptrs l_llvm
/\ no_next_key l_llvm m_llvm.


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
  (forall z, ptr <> (next_logical_key m, z)) -> next_logical_key m <> fst ptr.
Proof.
  intros.
  destruct ptr.
  unfold fst.
  intro H1.
  rewrite H1 in H.
  specialize H with (z:=z0).
  contradiction.
Qed.

Lemma aux2: 
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


Lemma get_val_mem_stack_add: forall g env l m k x i v,
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

(* Lemma RenvhAssign2 : forall env g l m i,
  RAlloc env l m ->
  Renvh env g l m ->
  Renvh env g l (match write m (FMapAList.alist_find (Name k) l) (DVALUE_I32 i) with inr m' => m' end).
Proof.
  unfold Renvh in *.
  intros env g l m i ptr m' HFind HWrite.
  split.
  + unfold get_val in *.
    split.
    - intros.
      setoid_rewrite HFind in H.
      setoid_rewrite HFind.
    
  + apply H1. auto.
Qed.
 *)

From Coq Require Import Classes.RelationClasses.

Lemma sym_neq : forall a b : Z, (a <> b)%Z -> b <> a.
Proof.
  intros.
  auto.
Qed.

Lemma lt_neq : forall a b : Z, (a < b)%Z -> a <> b.
Proof.
  intros a b H_lt H_eq.
  rewrite H_eq in H_lt.
  apply Z.lt_irrefl in H_lt.
  contradiction.
Qed.

Lemma unique_ptrs_holds : forall l x m,
unique_ptrs l ->
no_next_key l m ->
unique_ptrs (FMapAList.alist_add (Name x) (UVALUE_Addr (next_logical_key m, 0%Z)) l).
Proof.
intros.
unfold no_next_key in H0.
unfold unique_ptrs in *.
intros.
destruct (string_dec key x), (string_dec key' x); subst; try contradiction.
+ rewrite alist_find_add_eq in H2.
  apply names_neq in n.
  rewrite alist_find_neq in H3; auto.
  injection H2; intros; subst.
  simpl.
  apply sym_neq.
  apply lt_neq.
  apply H0 with (key:=key').
  assumption.
+ rewrite alist_find_add_eq in H3.
  apply names_neq in n.
  rewrite alist_find_neq in H2; auto.
  injection H3; intros; subst.
  simpl.
  apply lt_neq.
  apply H0 with (key:=key).
  assumption.
+ apply names_neq in n.
  apply names_neq in n0.
  rewrite alist_find_neq in H2; auto.
  rewrite alist_find_neq in H3; auto.
  apply H with key key'; auto.
Qed.
 

Lemma next_logical_key_mem_stack_add : forall m x i,
next_logical_key (mem_stack_add m x i) = ((next_logical_key m) + 1%Z)%Z.
Proof.
intros.
unfold mem_stack_add.
(* 
pose proof next_logical_key_alloc.

unfold next_logical_key.
unfold next_logical_key_mem.
simpl.
destruct write eqn:WRITE.
+ unfold write in WRITE.
  simpl in WRITE.
  rewrite get_logical_block_of_add_to_frame in WRITE.
  rewrite get_logical_block_of_add_logical_block in WRITE.
  simpl in WRITE.
  discriminate.
+ unfold logical_next_key.
  unfold write in WRITE.
  simpl in WRITE.
  rewrite get_logical_block_of_add_to_frame in WRITE.
  rewrite get_logical_block_of_add_logical_block in WRITE.
  simpl in WRITE.
  injection WRITE; intros; subst.
  simpl.
  unfold add_logical_block.
  destruct m.
  unfold add_to_frame.
  unfold add_logical_block_mem.
  destruct f.
  - destruct m.
    simpl. *) 
Admitted.


Lemma no_next_key_holds : forall l m x i,
no_next_key l m ->
no_next_key (FMapAList.alist_add (Name x) (UVALUE_Addr (next_logical_key m, 0%Z)) l) (mem_stack_add m x i).
Proof.
intros.
unfold no_next_key in *.
intros.
destruct (string_dec x key); subst.
+ rewrite alist_find_add_eq in H0.
  injection H0; intros; subst.
  simpl. 
  rewrite next_logical_key_mem_stack_add.
  lia.
+ apply names_neq in n.
  rewrite alist_find_neq in H0; auto.
  apply H in H0.
  rewrite next_logical_key_mem_stack_add.
  lia.
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

        apply get_val_mem_stack_add with (k:=k) (x:=x) (i:=i) (v:=v) in H0; auto.
        
  + split.
    split.

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

  - split.
    -- unfold Renvh in H0.
       specialize H0 with "" (Int32.repr 0%Z).
       destruct H0, H0, H1.
       apply unique_ptrs_holds; auto.
    -- unfold Renvh in H0.
       specialize H0 with "" (Int32.repr 0%Z).
       destruct H0, H0, H1.
       apply no_next_key_holds.
       auto.
Qed. 

Fixpoint addr_dec (a1 a2 : addr) : {a1 = a2} + {a1 <> a2}.
Proof.
  destruct a1, a2.
  decide equality. 
  apply Z.eq_dec.
  apply Z.eq_dec.
Defined.


Lemma read_same_after_write : forall m ptr i ,
allocated ptr m ->
read
    match write m ptr (DVALUE_I32 i) with
    | inl _ => empty_memory_stack
    | inr x1 => x1
    end ptr (DTYPE_I 32) = inr (UVALUE_I32 i).
Proof.
intros.
unfold write.
destruct get_logical_block eqn:EQ.
+ destruct l.
  destruct ptr.
  unfold read.
  simpl.
  rewrite get_logical_block_of_add_logical_block.
  Arguments add_all_index : simpl never.
  Arguments serialize_dvalue : simpl never.
  unfold read_in_mem_block.
  rewrite deserialize_serialize; try constructor.
+ apply allocated_get_logical_block in H.
  rewrite EQ in H.
  destruct H.
  discriminate.
Qed.

(* Lemma glb_same_after_write : forall m ptr i z1 ,
allocated (ptr, z1)  m ->
get_logical_block
      match write m (ptr, z1) (DVALUE_I32 (Int32.repr (Int32.unsigned i))) with
      | inl _ => empty_memory_stack
      | inr x1 => x1
      end ptr
 = inr (UVALUE_I32 (Int32.repr (Int32.unsigned i))).
Proof.
intros.
unfold write.
destruct get_logical_block eqn:EQ.
+ destruct l.
  destruct ptr.
  unfold read.
  simpl.
  rewrite get_logical_block_of_add_logical_block.
  Arguments add_all_index : simpl never.
  Arguments serialize_dvalue : simpl never.
  unfold read_in_mem_block.
  rewrite deserialize_serialize; try constructor.
+ apply allocated_get_logical_block in H.
  rewrite EQ in H.
  destruct H.
  discriminate.
Qed. *)


Lemma get_val_same_ptrs: forall g l m x i ptr,
allocated ptr m ->
FMapAList.alist_find (Name x) l = Some (UVALUE_Addr ptr) ->
get_val g l
  match write m ptr (DVALUE_I32 i) with
  | inl _ => empty_memory_stack
  | inr x1 => x1
  end x = Some i.
Proof.
intros.
unfold get_val in *.
rewrite H0 in *.
rewrite read_same_after_write; auto.
Qed.



(* Lemma get_val_diff_ptrs : forall g l m x ptr ptr' v i,
allocated (ptr, 0%Z) m ->
FMapAList.alist_find (Name x) l = Some (UVALUE_Addr (ptr', 0%Z)) ->
ptr <> ptr' ->
get_val g l m x = Some v ->
get_val g l
  match write m (ptr, 0%Z) (DVALUE_I32 (Int32.repr (Int32.unsigned i))) with
  | inl _ => empty_memory_stack
  | inr x1 => x1
  end x = Some v.
Proof.
intros.
unfold get_val in *.
rewrite H0.
rewrite H0 in H2.
destruct read eqn:EQ in H2; try discriminate.
destruct u; try discriminate.
injection H2; intros; subst; clear H2.
destruct write eqn:WRITE.
+ apply allocated_get_logical_block in H.
  unfold write in WRITE.
  destruct H.
  rewrite H in WRITE.
  destruct x0 in WRITE.
  destruct ptr in WRITE.
  simpl in WRITE.
  discriminate.
+ rewrite write_untouched with (m1:=m) (a:=ptr) (v:=(DVALUE_I32 (Int32.repr (Int32.unsigned i)))) (τ:=DTYPE_I 32); auto.
  - rewrite EQ.
    reflexivity.
  - constructor.
  - unfold no_overlap_dtyp.
    unfold no_overlap.




    
Qed. *)

Lemma get_val_diff_ptrs : forall g l m x ptr ptr' v i,
allocated ptr m ->
FMapAList.alist_find (Name x) l = Some (UVALUE_Addr ptr') ->
fst ptr <> fst ptr' ->
get_val g l m x = Some v ->
get_val g l
  match write m ptr (DVALUE_I32 i) with
  | inl _ => empty_memory_stack
  | inr x1 => x1
  end x = Some v.
Proof.
intros.
unfold get_val in *.
rewrite H0 in *.
destruct read eqn:EQ in H2; try discriminate.
destruct u; try discriminate.
injection H2; intros; subst; clear H2.
destruct write eqn:WRITE.
+ apply allocated_get_logical_block in H.
  unfold write in WRITE.
  destruct H.
  rewrite H in WRITE.
  destruct x0 in WRITE.
  destruct ptr in WRITE.
  simpl in WRITE.
  discriminate.
+ rewrite write_untouched with (m1:=m) (a:=ptr) (v:=(DVALUE_I32 i)) (τ:=DTYPE_I 32); auto.
  - rewrite EQ.
    reflexivity.
  - constructor.
  - unfold no_overlap_dtyp.
    unfold no_overlap.
    auto.    
Qed. 

Lemma can_write_allocated :
    forall ptr τ v m,
      write m ptr τ = inr v ->
      allocated ptr m.
  Proof.
    intros ptr τ v m READ.
    unfold write in READ.
    destruct (get_logical_block m (fst ptr)) eqn:LBLOCK.
    - destruct l.
      red. unfold get_logical_block, get_logical_block_mem in LBLOCK.
      apply lookup_member in LBLOCK.
      do 2 destruct m.
      cbn in LBLOCK.
      auto.
    - inversion READ.
    Qed.

From Coq Require Import FSets.FMapFacts.

Check IM.elements.

Definition keys {elt:Type} (m:IM.t elt) : list Z :=  fst (split (IM.elements m)).

Fixpoint split_alt {A:Type} {B:Type} (l:list (A*B) %type) : (list A * list B) % type:=
  match l with
    | nil => (nil, nil)
    | (x, y) :: l => (x :: (fst (split_alt l)), y :: (snd (split_alt l)))
  end.

Lemma split_alt_spec:
  forall {A:Type} {B:Type} (l:list (A*B) %type),
  split l = split_alt l.
Proof.
  intros.
  induction l.
  - auto.
  - simpl. intuition.
    rewrite IHl.
    remember (split_alt l) as l'.
    destruct l' as (lhs, rhs).
    auto.
Qed.

Lemma in_fst_split:
  forall {A:Type} {B:Type} (l:list (A*B)%type) (lhs:A),
  List.In lhs (fst (split l)) ->
  exists rhs, List.In (lhs, rhs) l.
Proof.
  intros.
  induction l.
  { inversion H. (* absurd *) }
  destruct a.
  rewrite split_alt_spec in H.
  simpl in H.
  destruct H.
  + subst.
    eauto using in_eq.
  + rewrite <- split_alt_spec in H.
    apply IHl in H; clear IHl.
    destruct H as (r, Hin).
    eauto using in_cons.
Qed.

  Lemma in_elements_to_in:
    forall {elt:Type} k e (m: IM.t elt),
    List.In (k, e) (IM.elements m) ->
    IM.In k m.
  Proof.
    intros.
    rewrite IP.F.elements_in_iff.
    exists e.
    apply InA_altdef.
    apply Exists_exists.
    exists (k,e).
    intuition.
  Qed.

  Lemma keys_spec_1:
    forall {elt:Type} (m:IM.t elt) (k:Z),
    List.In k (keys m) -> IM.In k m.
  Proof.
    intros.
    unfold keys in *.
    apply in_fst_split in H.
    destruct H as (e, H).
    apply in_elements_to_in with (e:=e).
    assumption.
  Qed.

  Lemma maps_to_impl_in_elements:
    forall {elt:Type} k (e:elt) m,
    IM.MapsTo k e m ->
    exists k', Z.eq k k' /\ List.In (k', e) (IM.elements (elt:=elt) m).
  Proof.
    intros.
    apply IM.elements_1 in H.
    apply InA_alt in H.
    destruct H as ((k', e'), (Heq, Hin)).
    inversion Heq.
    simpl in *.
    subst.
    exists k'.
    intuition.
  Qed.

  Lemma keys_spec_2:
    forall {elt:Type} (m:IM.t elt) (k:Z),
    IM.In k m ->
    exists k', Z.eq k k' /\ List.In k' (keys m).
  Proof.
    intros.
    unfold keys in *.
    destruct H as (e, H).
    apply maps_to_impl_in_elements in H.
    destruct H as (k', (Heq, Hin)).
    apply in_split_l in Hin.
    exists k'.
    intuition.
  Qed.


Lemma map_fst_split {A B} : forall (l: list (A*B)),
map fst l = fst (split l).
Proof.
intros.
induction l.
+ unfold map.
  reflexivity.
+ destruct a.
  simpl.
  destruct split.
  simpl in *.
  unfold map.
  simpl.
  rewrite <- IHl.
  reflexivity.
Qed.


 Lemma keys_spec (k_eq: forall k k', Z.eq k k' <-> k = k'):
    forall {elt:Type} (m:IM.t elt) (k:Z),
    IM.In k m <-> List.In k (keys m).
  Proof.
    intros.
    split.
    - intros.
      apply keys_spec_2 in H.
      destruct H as (k', (Heq, H)).
      unfold Z.eq in Heq; subst.
      assumption.
    - apply keys_spec_1.
  Qed.

Lemma keys_sorted : forall m,
Sorted (Z.lt) (keys (elt:=logical_block) m).
Proof.
intros.
unfold keys.
rewrite <- map_fst_split.
pose proof IM.elements_3.
specialize H with (m:=m) (elt:=logical_block).
induction (IM.elements m).
+ unfold map.
  auto.
+ unfold map.
  apply Sorted_inv in H.
  destruct H.
  apply Sorted_cons.
  - unfold map in IHl.
    apply IHl; auto.
  - destruct a.
    simpl.

    destruct l as [ | (k', l') tl].
    -- simpl.
       auto.
    -- simpl in H0.
       unfold IM.lt_key in H0.
       unfold IM.Raw.Proofs.PX.ltk in H0.
       apply HdRel_inv in H0.
       simpl in H0.
       apply HdRel_cons.
       simpl.
       assumption.
Qed.

Lemma in_cons_iff2 :
forall (x : Z) z l l',
In x (z :: l) <-> In x (z :: l') ->
NoDup (z :: l) ->
NoDup (z :: l') ->
length l = length l' ->
In x l <-> In x l'.
Proof.
intros.
pose proof H.
simpl in H.
destruct (Z.eq_dec x z); subst.
+ clear H.
  inversion H0; subst; simpl.
  inversion H1; subst; simpl.
  split; intros; contradiction.
+ destruct H.
  split.
  - intros.
    assert (z = x \/ In x l); auto.
    apply H in H6.
    destruct H6; subst; try contradiction.
    assumption.
  - intros.
    assert (z = x \/ In x l'); auto.
    apply H4 in H6.
    destruct H6; subst; try contradiction.
    assumption.
Qed.

Lemma InA_In {A} : forall x l,
InA eq x l <-> In (A:=A) x l.
Proof.
split.
+ intros.
  apply InA_alt in H.
  destruct H, H; subst.
  assumption.
+ intros.
  apply InA_alt.
  exists x.
  auto.
Qed.

Lemma not_InA_In {A} : forall x l,
~ InA eq x l <-> ~ In (A:=A) x l.
Proof.
split.
+ unfold not in *.
  intros.
  apply InA_In in H0.
  apply H in H0.
  contradiction.
+ unfold not in *.
  intros.
  apply InA_In in H0.
  apply H in H0.
  contradiction.
Qed.

Lemma nodupA_nodup {A} : forall l,
NoDupA eq l <-> NoDup (A:=A) l.
Proof.
induction l.
+ split; intros.
  - apply NoDup_nil.
  - apply NoDupA_nil.
+ split; intros.
  - inversion H; subst.
    apply IHl in H3.
    apply not_InA_In in H2.
    apply NoDup_cons; auto.
  - inversion H; subst.
    apply IHl in H3.
    apply not_InA_In in H2.
    apply NoDupA_cons; auto.
Qed.


Lemma in_cons_iff :
forall (x : Z) z l l',
In x (z :: l) <-> In x (z :: l') ->
NoDup (z :: l) ->
NoDup (z :: l') ->
length l = length l' ->
In x l <-> In x l'.
Proof.
intros.
pose proof H.
simpl in H.
destruct (Z.eq_dec x z); subst.
+ clear H.
  inversion H0; subst; simpl.
  inversion H1; subst; simpl.
  split; intros; contradiction.
+ destruct H.
  split.
  - intros.
    assert (z = x \/ In x l); auto.
    apply H in H6.
    destruct H6; subst; try contradiction.
    assumption.
  - intros.
    assert (z = x \/ In x l'); auto.
    apply H4 in H6.
    destruct H6; subst; try contradiction.
    assumption.
Qed.

Lemma sorted_nodup : forall l,
Sorted Z.lt l ->
NoDup l.
Proof.
induction l; intros.
+ apply NoDup_nil.
+ apply Sorted_inv in H.
  destruct H.
  apply NoDup_cons; auto.
  intros Hin.
  induction l.
  - contradiction.
  - apply IHl0.
    -- intros.
       apply IHl in H.
       inversion H; auto.
    -- inversion H; auto.
    -- inversion H; subst.
       apply HdRel_inv in H0.
       destruct l.
      ---- apply HdRel_nil.
      ---- apply HdRel_cons.
        inversion H4. subst.
        apply Z.lt_trans with a0; assumption.   
    -- destruct (Z.eq_dec a a0); subst.
       --- apply HdRel_inv in H0.
           apply Z.lt_irrefl in H0.
           contradiction.
       --- simpl in Hin.
           destruct Hin; subst; try contradiction.
           assumption.
Qed.

Lemma keys_nodup : forall m,
NoDupA Z.eq (keys (elt:=logical_block) m).
Proof.
intros.
pose proof keys_sorted.
apply sorted_nodup with (l:=keys m) in H.
apply nodupA_nodup.
assumption.
Qed.

Lemma sorted_mid_element : forall a b l,
Sorted Z.lt (a :: b :: l) ->
Sorted Z.lt (a :: l).
Proof.
intros.
inversion H; subst.
inversion H2; subst.
apply HdRel_inv in H3.
apply Sorted_cons; auto.
destruct l; auto.
apply HdRel_cons.
inversion H5. subst.
apply Z.lt_trans with b; assumption.
Qed.

Lemma in_le :
forall a x l,
In x l ->
Sorted Z.lt (a :: l) ->
(a < x)%Z.
Proof.
intros.
inversion H0; subst.
induction l.
+ simpl in H.
  contradiction.
+ destruct (Z.eq_dec x a0); subst.
  - apply HdRel_inv in H4. 
    assumption.
  - simpl in H.
    destruct H; subst; try contradiction.
    apply sorted_mid_element in H0.
    inversion H0; subst.
    apply IHl; auto.
Qed.

Lemma absurd : forall a b l l',
In a l' ->
In b l ->
Sorted (Z.lt) (a :: l) ->
Sorted (Z.lt) (b :: l') ->
False.
Proof.
induction l, l'; try (intros; simpl; contradiction).
intros.
apply IHl with (l':=l').
+ assert ((b < a)%Z). {
    apply in_le with (l:= (z :: l')); auto.
  }
  assert ((a < b)%Z). {
    apply in_le with (l:= (a0 :: l)); auto.
  }
  apply (Z.lt_asymm b a) in H3.
  contradiction.
+ assert ((b < a)%Z). {
    apply in_le with (l:= (z :: l')); auto.
  }
  assert ((a < b)%Z). {
    apply in_le with (l:= (a0 :: l)); auto.
  }
  apply (Z.lt_asymm b a) in H3.
  contradiction.
+ apply sorted_mid_element with (b:=a0); auto.
+ apply sorted_mid_element with (b:=z); auto.
Qed.



Lemma same_size_sorted_in_eq :
forall l l',
Sorted (Z.lt) l ->
Sorted (Z.lt) l' ->
NoDup l ->
NoDup l' ->
length l = length l' ->
(forall x, In x l <-> In x l') ->
l = l'.
Proof.
induction l, l'.
+ intros. reflexivity.
+ intros. unfold length in H1. discriminate.
+ intros. unfold length in H1. discriminate.
+ intros.
  destruct (Z.eq_dec a z); subst.
  - apply Sorted_inv in H, H0.
    destruct H, H0.
    simpl in H3.
    injection H3; intros.
    pose proof H1.
    pose proof H2.
    apply NoDup_cons_iff in H8; destruct H8.
    apply NoDup_cons_iff in H9; destruct H9.

    rewrite IHl with (l':=l'); auto.
    intros.
    apply in_cons_iff with (z:=z); auto.
  - exfalso.
    pose proof H4.
    simpl in H4, H5.
    destruct H4 with (x := z); clear H6.
    destruct H5 with (x := a); clear H8.
    assert (a = z \/ In z l); auto; clear H7.
    assert (z = a \/ In a l'); auto; clear H6.
    destruct H7, H8; subst; try contradiction.
    inversion H; subst.
    apply absurd with (a:=a) (l:=l) (b:=z) (l':=l'); auto.
Qed.

Lemma cardinal_holds_bal : forall t1 t2 e k,
S (IM.Raw.cardinal t1 + IM.Raw.cardinal t2) = IM.Raw.cardinal (elt:=logical_block) (IM.Raw.bal t1 k e t2).
Proof.
intros.
unfold IM.Raw.bal.
destruct (Int.Z_as_Int.gt_le_dec (IM.Raw.height t1) (Int.Z_as_Int.add (IM.Raw.height t2) Int.Z_as_Int._2)).
+ destruct t1.
  - cbn.
    reflexivity.
  - destruct (Int.Z_as_Int.ge_lt_dec (IM.Raw.height t1_1) (IM.Raw.height t1_2)).
    -- cbn. lia.
    -- destruct t1_2.
      --- cbn. lia.
      --- cbn. lia.
+ destruct t2.
  - cbn.
    destruct (Int.Z_as_Int.gt_le_dec Int.Z_as_Int._0 (Int.Z_as_Int.add (IM.Raw.height t1) Int.Z_as_Int._2)).
    -- cbn. reflexivity.
    -- cbn. reflexivity.
  - destruct (Int.Z_as_Int.gt_le_dec (IM.Raw.height (IM.Raw.Node t2_1 k0 l0 t2_2 t)) (Int.Z_as_Int.add (IM.Raw.height t1) Int.Z_as_Int._2)).
    -- destruct (Int.Z_as_Int.ge_lt_dec (IM.Raw.height t2_2) (IM.Raw.height t2_1)).
      --- cbn. lia.
      --- destruct t2_1.
          ---- cbn. lia.
          ---- cbn. lia.
      -- cbn. lia.
Qed.


Lemma existing_key_map_elements:
  forall m (k:Z) v,
  IM.In (elt:=logical_block) k m ->
  IM.cardinal m = IM.cardinal (IM.add k v m).
Proof.
  intros.
  destruct m.
  induction this.
  + repeat rewrite IP.cardinal_fold.
    apply IM.mem_1 in H.
    cbn in H.
    discriminate.
  + cbn in *.
    destruct (OrderedTypeEx.Z_as_OT.compare k k0) eqn:test.
    - pose proof H as H0.
      unfold IM.In in H.
      apply IM.Raw.Proofs.In_alt in H.
      eapply IM.Raw.Proofs.In_node_iff in H.
      rewrite <- cardinal_holds_bal.
      destruct H. 
      -- apply IM.Raw.Proofs.In_alt in H.
         inversion is_bst.
         rewrite IHthis1 with (is_bst := H5); auto.
      -- destruct H.
         --- subst.
             unfold OrderedTypeEx.Z_as_OT.lt in l.
             assert (~ (k0 < k0)%Z).
             apply Z.lt_irrefl.
             contradiction.
         --- (*Esto no puede ser, como va a estar k en this2 si es k < k0 y está ordenado *)
            unfold OrderedTypeEx.Z_as_OT.lt in l.
            pose proof l.
            inversion is_bst; subst.
            apply IM.Raw.Proofs.gt_tree_trans with (y:=k) in H10; auto.
            apply IM.Raw.Proofs.gt_tree_not_in in H10.
            contradiction.
    - cbn. reflexivity.
    - pose proof H as H0.
      unfold IM.In in H.
      apply IM.Raw.Proofs.In_alt in H.
      eapply IM.Raw.Proofs.In_node_iff in H.
      rewrite <- cardinal_holds_bal.
      destruct H.
      -- unfold OrderedTypeEx.Z_as_OT.lt in l.
         pose proof l.
         pose proof is_bst.
         inversion H2; subst.
         apply IM.Raw.Proofs.lt_tree_trans with (y:=k) in H10; auto.
         apply IM.Raw.Proofs.lt_tree_not_in in H10.
         contradiction.

      -- destruct H.
         --- subst.
             unfold OrderedTypeEx.Z_as_OT.lt in l.
             assert (~ (k0 < k0)%Z).
             apply Z.lt_irrefl.
             contradiction.
         --- apply IM.Raw.Proofs.In_alt in H.
             inversion is_bst.
             rewrite IHthis2 with (is_bst := H7); auto.
Qed.

Lemma length_keys_same_elements : forall m,
length (keys m) = length (IM.elements (elt:=logical_block) m).
Proof.
unfold keys.
intros.
rewrite split_length_l.
reflexivity.
Qed.

Lemma add_in_same_keys :
forall m k v,
IM.In k m ->
keys m = keys (elt:=logical_block) (IM.add k v m).
Proof.
intros.
pose proof keys_sorted.
pose proof keys_sorted.
specialize H0 with (m:=m).
specialize H1 with (m:=IM.add k v m).
pose proof H.
apply existing_key_map_elements with (v:=v) in H.
repeat erewrite IM.cardinal_1 in H.

pose proof keys_nodup as NODUP1.
pose proof keys_nodup as NODUP2.

specialize NODUP1 with (m:=m).
specialize NODUP2 with (m:=(IM.add k v m)).
apply nodupA_nodup in NODUP1.
apply nodupA_nodup in NODUP2.

apply same_size_sorted_in_eq; auto.
+ repeat rewrite <- length_keys_same_elements in H.
  assumption.
+ intros.
  destruct (Z.eq_dec k x); subst.
  - pose proof H2.
    apply keys_spec in H2; try (unfold Z.eq; reflexivity).
    assert (x = x \/ IM.In (elt:=logical_block) x m). left; reflexivity.
    rewrite <- IP.F.add_in_iff with (e:=v) in H4.
    apply keys_spec in H4; try (unfold Z.eq; reflexivity).
    apply keys_spec in H3; try (unfold Z.eq; reflexivity).
    split; intros; auto.
  - split.
    -- intros.
       apply keys_spec in H3; try (unfold Z.eq; reflexivity).
       apply keys_spec; try (unfold Z.eq; reflexivity).
       rewrite IP.F.add_in_iff; right; assumption.
    -- intros.
       apply keys_spec in H3; try (unfold Z.eq; reflexivity).
       apply keys_spec; try (unfold Z.eq; reflexivity).
       apply IP.F.add_neq_in_iff in H3; auto.
Qed.

Import ListNotations.

(* Lemma add_in_diff_keys : forall k m v,
~ IM.In k m ->
(keys (IM.add k v m)) = ((keys m) ++ [k]).
Proof. *)

Lemma next_logical_key_after_write:
forall m ptr i,
allocated ptr m ->
next_logical_key m = next_logical_key match write m ptr (DVALUE_I32 i) with
                          | inl _ => empty_memory_stack
                          | inr x1 => x1
                          end.
Proof.
intros.
unfold next_logical_key.
unfold next_logical_key_mem.
unfold logical_next_key.
rewrite map_fst_split.
unfold write.
destruct get_logical_block eqn:DEST_GLB.
+ destruct l.
  destruct ptr.
  simpl.
  unfold add_logical_block.
  unfold add_logical_block_mem.
  destruct m, m.
  unfold add.
  pose proof add_in_same_keys.
  unfold keys in H0.
  simpl.
  unfold allocated in H.
  simpl in H.
  rewrite H0 with (m:=l) (k:=z) (v:=(LBlock size (add_all_index (serialize_dvalue (DVALUE_I32 i)) z0 bytes) concrete_id)).
  rewrite map_fst_split.
  reflexivity.
  unfold member in H.
  apply IM.mem_2 in H.
  assumption.
+ cbn.
  apply allocated_get_logical_block in H.
  destruct H.
  rewrite H in DEST_GLB.
  discriminate.
Qed.

Lemma no_next_key_after_write : forall l m ptr i,
allocated ptr m ->
no_next_key l m ->
no_next_key l
  match write m ptr (DVALUE_I32 i) with
  | inl _ => empty_memory_stack
  | inr x1 => x1
  end.
Proof.
unfold no_next_key.
intros.
apply H0 in H1.
rewrite <- next_logical_key_after_write; auto.
Qed.



Lemma maximumBy_cons : forall a l,
maximumBy Z.leb (-1)%Z (a :: l) = Z.max a (maximumBy Z.leb (-1)%Z l).
Proof.
Admitted.

Lemma maximumBy_inor : forall l,
In (maximumBy Z.leb (-1)%Z l) l \/ (maximumBy Z.leb (-1)%Z l) = (-1)%Z .
Admitted.

Lemma maximumBy_inor2 : forall l1 l2,
(forall x : Z, In x l1 <-> In x l2) ->
In (maximumBy Z.leb (-1)%Z l1) l2 \/ (maximumBy Z.leb (-1)%Z l1) = (-1)%Z.
Admitted.

Lemma maximumBy_In: forall l1 l2,
(forall x, In x l1 <-> In x l2) ->
maximumBy Z.leb (-1)%Z l1 = maximumBy Z.leb (-1)%Z l2.
Proof.
intros.
assert (In (maximumBy Z.leb (-1)%Z l1) l2 \/ (~(In (maximumBy Z.leb (-1)%Z l1) l2) /\ (maximumBy Z.leb (-1)%Z l1) = (-1)%Z)). give_up.
assert (In (maximumBy Z.leb (-1)%Z l2) l1 \/ (~(In (maximumBy Z.leb (-1)%Z l2) l1) /\ (maximumBy Z.leb (-1)%Z l2) = (-1)%Z)). give_up.
destruct H0, H1.
+ apply maximumBy_Z_correct with (def:=(-1)%Z) in H0.
  apply maximumBy_Z_correct with (def:=(-1)%Z) in H1.
  give_up.
+ apply H in H0.
+
+

Admitted.

Lemma greater_is_same_as_adding : forall l k,
(k > maximumBy Z.leb (-1)%Z l)%Z ->
maximumBy Z.leb (-1)%Z (l ++ [k]) = k.
Admitted.

Lemma idk : forall k m v,
(k > maximumBy Z.leb (-1)%Z (keys m))%Z ->
maximumBy Z.leb (-1)%Z (keys (elt:=logical_block) (IM.add k v m)) = k.
Proof.
intros.
destruct (IP.F.In_dec m k).
+ exfalso. give_up.
+ assert(forall x, In x (keys (IM.add k v m)) <-> In x (keys m ++ [k])). give_up.
  apply maximumBy_In in H0.
  rewrite greater_is_same_as_adding in H0; auto.
Admitted.

Lemma next_logical_key_alloc : forall m m' ptr,
allocate m (DTYPE_I 32) = inr (m', ptr) ->
next_logical_key m' = ((next_logical_key m) + 1%Z)%Z.
Proof.
intros.
unfold next_logical_key.
unfold next_logical_key_mem.
unfold logical_next_key.
unfold allocate in H.
simpl in H.
injection H.
intros.
clear H H0.
unfold add_to_frame in H1.
destruct add_logical_block eqn:DES in H1.
unfold add_logical_block in DES.
destruct m, m'.
destruct f.
Opaque Z.add.
simpl in *.
+ injection DES; intros.
  rewrite <- H0 in H1.
  injection H1; intros.
  rewrite <- H3.
  clear DES H1 H H0 H2 H3.
  unfold next_logical_key.
  unfold next_logical_key_mem.
  unfold logical_next_key.
  simpl.
  unfold add_logical_block_mem.
  unfold add.
  destruct m.
  simpl.
  set (max:=maximumBy Z.leb (-1)%Z (map fst (IM.elements (elt:=logical_block) l))).
  rewrite map_fst_split.
  pose proof idk.
  unfold keys in H.
  rewrite H.
  lia.
  rewrite <- map_fst_split.
  lia.
+ injection DES; intros.
  rewrite <- H0 in H1.
  injection H1; intros.
  rewrite <- H3.
  clear DES H1 H H0 H2 H3.
  unfold next_logical_key.
  unfold next_logical_key_mem.
  unfold logical_next_key.
  simpl.
  unfold add_logical_block_mem.
  unfold add.
  destruct m.
  simpl.
  set (max:=maximumBy Z.leb (-1)%Z (map fst (IM.elements (elt:=logical_block) l))).
  rewrite map_fst_split.
  pose proof idk.
  unfold keys in H.
  rewrite H.
  lia.
  rewrite <- map_fst_split.
  lia.
Qed.


Lemma get_val_ineq :
forall g l m ptr ptr' i k,
allocated ptr m ->
FMapAList.alist_find (Name k) l = Some (UVALUE_Addr ptr') ->
(fst ptr) <> (fst ptr') ->
get_val g l match write m ptr (DVALUE_I32 i) with
                 | inl _ => empty_memory_stack
                 | inr x1 => x1
                 end k = get_val g l m k.
Proof.
intros.
unfold get_val in *.
rewrite H0.
destruct (write m ptr (DVALUE_I32 i)) eqn:DES_WRITE.
+ unfold write in DES_WRITE.
  apply allocated_get_logical_block in H.
  destruct H.
  rewrite H in DES_WRITE.
  destruct x, ptr; simpl in DES_WRITE.
  discriminate.
+ apply write_untouched with (τ:=(DTYPE_I 32)) (τ':=(DTYPE_I 32)) (a':=ptr') in DES_WRITE.
  - rewrite DES_WRITE.
    reflexivity.
  - constructor.
  - unfold no_overlap_dtyp.
    unfold no_overlap.
    auto.
Qed.

Lemma Renv_holds : forall e g l m i x ptr i0,
allocated ptr m ->
FMapAList.alist_find (Name x) l = Some (UVALUE_Addr ptr) ->
FMapAList.alist_find x e = Some i0 ->
Renvh e g l m ->
Renvh (FMapAList.alist_add x i e) g l
  match write m ptr (DVALUE_I32 i) with
  | inl _ => empty_memory_stack
  | inr x1 => x1
  end.
Proof.
intros.
unfold Renvh in *.
split.
+ split.
  - intros.
    destruct (String.eqb_spec k x); subst.
    -- rewrite get_val_same_ptrs; auto.
       apply alist_In_add_eq in H3.
       subst.
       reflexivity.
    -- 
       assert (forall key key' ptr ptr', key <> key' -> FMapAList.alist_find (Name key) l = Some (UVALUE_Addr ptr) -> FMapAList.alist_find (Name key') l = Some (UVALUE_Addr ptr') -> fst ptr <> fst ptr') as DIFF. {
       unfold unique_ptrs in H2.
       apply H2; auto.

        }
       unfold alist_In in H3.
       apply In_add_In_ineq in H3; auto.
       apply H2 in H3.
       pose proof H3.
       unfold get_val in H4.
       destruct (FMapAList.alist_find (Name k) l) eqn:EQ_FIND in H4; try discriminate.
       destruct u eqn:d in H4; try discriminate; subst.
       apply get_val_diff_ptrs with (ptr':=a); auto.
       apply DIFF with (key:=x) (key':=k); auto. 
  - intros.
    destruct (String.eqb_spec k x); subst.
    -- rewrite get_val_same_ptrs in H3; auto.
       unfold alist_In.
       rewrite alist_find_add_eq.
       assumption.
    -- assert (forall key key' ptr ptr', key <> key' -> FMapAList.alist_find (Name key) l = Some (UVALUE_Addr ptr) -> FMapAList.alist_find (Name key') l = Some (UVALUE_Addr ptr') -> fst ptr <> fst ptr') as DIFF. {
       unfold unique_ptrs in H2.
       apply H2; auto.

        }
       pose proof H3.
       unfold get_val in H3.
       destruct (FMapAList.alist_find (Name k) l) eqn:DES_PTR; try discriminate.
       destruct u; try discriminate.

       specialize DIFF with x k ptr a.

       rewrite get_val_ineq with (ptr':=a) in H4; auto.
       apply H2 in H4.
       apply In_In_add_ineq; auto.
+ split.
  split.
  - intros.
    destruct (String.eqb_spec k x); subst.
    -- rewrite alist_find_add_eq in H3; discriminate.
    -- rewrite alist_find_neq in H3; auto.
       apply H2 in H3; auto.
  - intros.
    destruct (String.eqb_spec k x); subst.
    -- rewrite H0 in H3.
       discriminate.
    -- rewrite alist_find_neq; auto.
       apply H2; auto.
- split.
  -- apply H2;auto.
  -- apply no_next_key_after_write; auto.
     specialize H2 with (k:="") (v:=Int32.repr 0%Z).
     destruct H2, H3, H4.
     assumption.
Qed.



