From ASL Require Import
  Ast Denotation CompilerCFG CorrectnessCFG AslFacts Utils.

From Coq Require Import
ZArith List String Classes.RelationClasses.


From Vellvm Require Import
  Semantics Syntax TopLevel Theory Utils.PropT  Utils.AListFacts Numeric.Integers Handlers.MemoryTheory Utilities. 

From ITree Require Import
  ITree ITreeFacts KTree KTreeFacts Events.StateFacts Events.MapDefaultFacts Events.StateFacts. 

From ExtLib Require Import
RelDec Tactics.

Import ITreeNotations.
Import ListNotations.
Import SemNotations.

Open Scope list_scope.
Open Scope string_scope.

Definition alist_In_uint32 {K R RD_K} k m v :=
  @FMapAList.alist_find K R RD_K Z k m = Some (trim_int_u32 v)%Z.

Definition Renv (env_asl : Denotation.env) (g_llvm : global_env) (l_llvm : local_env) (m_llvm : memory_stack) : Prop :=
forall k v, alist_In_uint32 k env_asl v <-> (get_val g_llvm l_llvm m_llvm k) =  Some (trim_int_u32 v). 

Definition eutt_inv (r1 : (Denotation.env * unit)) (r2 : memory_stack * (local_env * (global_env * uvalue))) : Prop :=
let asl_env := fst r1 in
let m_llvm := fst r2 in
let l_llvm := fst (snd r2) in
let g_llvm := fst (snd (snd r2)) in
  Renv asl_env g_llvm l_llvm m_llvm.

Definition bisimilar (t1 : itree (ImpState +' CallE +' PickE +' UBE +' DebugE +' FailureE) unit) (t2 : itree (instr_E) uvalue)  :=
  forall g_llvm l_llvm m_llvm g_asl,
    Renv g_asl g_llvm l_llvm m_llvm ->
      eutt eutt_inv
       (interp_asl t1 g_asl)
       (ℑ3 t2 g_llvm l_llvm m_llvm).

Definition TT {A B}: A -> B -> Prop  := fun _ _ => True.
  Hint Unfold TT: core.

From Coq Require Import Lia.


Lemma z_is_z : forall z, (0 <= z <= Int32.max_unsigned)%Z -> Int32.unsigned (Int32.repr z) = z.
Proof.
  intros.
  destruct z.
  + auto.
  + apply Int32.unsigned_repr. auto.
  + destruct H. destruct H. auto.
Qed.


(* Lemma uvalue_eq:
  forall (u : uvalue) (v : Z),
    match u with
    | UVALUE_I32 i => Some (Int32.intval i)
    | _ => None
    end = Some (Int32.intval (Int32.repr v)) ->
    u = UVALUE_I32 (Int32.repr v).
Proof.
  intros.
  destruct u; try discriminate.
  apply int32_from_uvalue_eq.
Qed.

Lemma test : forall u v, match u with
| UVALUE_I32 i => Some (Int32.intval i)
| _ => None
end = Some (Int32.intval (Int32.repr v)) -> u = UVALUE_I32 (Int32.repr v).
Proof.
   intros.
  remember (UVALUE_I32 (Int32.repr v)) as u_repr_v.
  assert (Hdec : {u = u_repr_v} + {u <> u_repr_v}) by apply uvalue_eq_dec.
  From Coq Require Import Program.Equality.
  dependent destruction Hdec.
  - assumption.
  - exfalso. (* derive a contradiction *)
    destruct u; try discriminate H.
    + inversion H. subst. apply n. reflexivity.
       *)

Lemma test : forall l_llvm m_llvm m x v, match FMapAList.alist_find (Name x) (FMapAList.alist_add (Name x) (UVALUE_Addr (next_logical_key m_llvm, 0%Z)) l_llvm) with
            | Some (UVALUE_Addr ptr) =>
                match read m ptr (DTYPE_I 32) with
                | inr (UVALUE_I32 i) => Some (Int32.unsigned i)
                | _ => None
                end
            | _ => None
            end = Some (trim_int_u32 v) <-> read m (next_logical_key m_llvm, 0%Z) (DTYPE_I 32) = inr (UVALUE_I32 (Int32.repr v)).
Proof.
  split.
  + intros.
    rewrite alist_find_add_eq in H.
    apply correct_int_read in H.
    auto.
  + intros.
    rewrite alist_find_add_eq.
    apply correct_int_read.
    auto.
Qed.

Lemma read_new_in_memstack : forall m x z v,
read (mem_stack_add m x z) (next_logical_key m, 0%Z) (DTYPE_I 32) =
            inr (UVALUE_I32 (Int32.repr v)) ->
Int32.repr v = Int32.repr z.
Proof.
  intros.
  unfold mem_stack_add in H. simpl in H.
  Arguments add_all_index : simpl never.
  Arguments serialize_dvalue : simpl never.
  unfold write in H. 
  rewrite get_logical_block_add_to_frame in H. 
  rewrite get_logical_block_of_add_logical_block in H.
  unfold read in H.
  simpl in H.
  rewrite get_logical_block_of_add_logical_block in H.
  unfold read_in_mem_block in H.
  rewrite deserialize_serialize in H.
  + simpl in H. injection H as Heq. rewrite extract_intval in Heq. rewrite extract_intval in Heq.
    pose proof trim_int_u32_inrange.

    unfold trim_int_u32 in Heq. auto.

  assert (write
          (add_to_frame
             (add_logical_block (next_logical_key m) (make_empty_logical_block (DTYPE_I 32)) m)
             (next_logical_key m)) (next_logical_key m, 0%Z) (DVALUE_I32 (Int32.repr z)) = inr empty_memory_stack).
  {
    unfold write.
    rewrite get_logical_block_add_to_frame. 
    rewrite get_logical_block_of_add_logical_block .
    Arguments add_all_index : simpl never.
    Arguments serialize_dvalue : simpl never.
    simpl make_empty_logical_block.
    simpl.
    
  }
  unfold write in H.

(* We need to prove that if every element holds Renv, and we add a new variable called "x" with value z, it will still hold.*)
Lemma Renv_write_local:
    forall (x : string) (z : Z) (env_asl : env) (g_llvm : global_env) (l_llvm : local_env) (m_llvm : memory_stack) ,
      Renv env_asl g_llvm l_llvm m_llvm ->
      Renv (FMapAList.alist_add x z env_asl) g_llvm (FMapAList.alist_add (Name x) (UVALUE_Addr (next_logical_key m_llvm, 0%Z)) l_llvm)
      (mem_stack_add m_llvm x z).
  Proof.
    intros x z env_asl g_llvm l_llvm m_llvm H0 k v.
    unfold Renv, get_val.
    split.
    (*First, we need to ensure that every variable-value pair inside env_asl, implies it's also in llvm memory.*)
    + destruct (String.eqb_spec k x).
      (* We analyze the case where the variable added was in the Renv relationship before, so its being overwritten.*)
      - subst.
        unfold alist_In_uint32.
        intros.
        rewrite alist_find_add_eq in H.
        assert (0 <= z <= Int32.max_unsigned)%Z. { 
          inversion H.
          apply trim_int_u32_inrange.
        }
        destruct H.
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
        simpl. f_equal. apply z_is_z; auto.
      - 
      (* We analyze the case where the variable added is new*)
        unfold alist_In_uint32.
        intros.
        assert (FMapAList.alist_find k (FMapAList.alist_add x z env_asl) = FMapAList.alist_find k env_asl). {
          apply alist_find_neq . auto.
        }
        rewrite H1 in H.
        unfold Renv in H0.
        unfold alist_In_uint32 in H0.
        unfold get_val in H0.
        apply H0 in H.
        rewrite alist_find_neq.
        -- destruct (FMapAList.alist_find (Name k) l_llvm); try discriminate.
           destruct u; try discriminate.
           unfold trim_int_u32.
           unfold Int32.unsigned .
           unfold trim_int_u32 in H.
           unfold Int32.unsigned in H.
           apply correct_int_read.
           apply correct_int_read in H.
           pose proof same_read_mem_stack_add.
           auto.
        -- (* We prove that k <> x -> Name k <> Name x *)
           unfold not.
           intros H'.
           inversion H'.
           contradiction.

   + intros Mem_value.
     unfold alist_In_uint32.
     destruct (String.eqb_spec k x).
     - subst.
       rewrite alist_find_add_eq. 
       apply test in Mem_value.

       

Theorem compiler_correct (s:stmt) :
  bisimilar (denote_asl s) (denote_cfg (compile_cfg s)).
Proof.
  unfold bisimilar.
  intros.
  induction s.
  3:{
    unfold denote_cfg. simpl.
    unfold CompilerCFG.empty_block.
    rewrite simpl_block.
    rewrite denote_code_nil.
    rewrite bind_ret_.
    rewrite bind_ret_.
    rewrite interp_cfg3_ret.
    rewrite interp_asl_ret.
    red. apply eqit_Ret.
    unfold eutt_inv.
    auto.
  }
  +unfold denote_cfg. simpl.
    unfold CompilerCFG.empty_block.
    destruct e.
    rewrite simpl_block.
    rewrite bind_bind.
    setoid_rewrite bind_ret_.
    unfold gen_alloc.
    rewrite denote_code_cons.
    rewrite interp_cfg3_bind.
    setoid_rewrite denote_code_singleton.
    rewrite simpl_alloca_assign.
    rewrite bind_ret_.
    rewrite interp_cfg3_ret.
    rewrite interp_asl_SetVar.
    red. apply eqit_Ret.
    unfold eutt_inv.
    simpl.
    

    unfold Renv.
    unfold Renv in H.

    

    rewrite <- H.
    rewrite Renv_get_val_add.


    assert(FMapAList.alist_find (Name k) (FMapAList.alist_add (Name x) (UVALUE_Addr (next_logical_key m_llvm, 0%Z)) l_llvm) = Some (UVALUE_Addr ptr)).
    {

    }
    rewrite alist_In_add_eq.
    simpl.




  