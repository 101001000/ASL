
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

Ltac simpl_iter :=
  unfold CategoryOps.iter, Iter_Kleisli, Basics.iter, MonadIter_itree.

Open Scope list_scope.
Open Scope string_scope.


Definition e_prog :=
TLE_Definition {|
  df_prototype := {|dc_name := (Name "main");
                    dc_type := (TYPE_Function (TYPE_I 32%N) []);
                    dc_param_attrs := ([], []);
                    dc_linkage := None;
                    dc_visibility := None;
                    dc_dll_storage := None;
                    dc_cconv := None;
                    dc_attrs := [];
                    dc_section := None;
                    dc_align := None;
                    dc_gc := None|};
  df_args := [];
  df_instrs := (
                {|
                  blk_id := (Name "entry");
                  blk_phis := [];
                  blk_code := [];
                  blk_term := TERM_Ret ((TYPE_I 32%N), (EXP_Integer (1)%Z));
                  blk_comments := None
                |}
                , nil (A:=block typ))
                |}.

Check e_prog.
Check mcfg_of_tle.


Definition e_test : itree L0 uvalue :=
 denote_vellvm (DTYPE_I 32%N) "main" [] (convert_types (mcfg_of_tle [e_prog])). 

Theorem empty_env : build_global_environment (convert_types (mcfg_of_tle [e_prog])) ≈ r <- trigger (Alloca DTYPE_Pointer);; trigger (GlobalWrite (Name "main") r);; Ret tt.
Proof.
unfold build_global_environment. simpl.
unfold initialize_globals. simpl.
unfold allocate_globals. simpl.
setoid_rewrite bind_ret_.
setoid_rewrite translate_ret.
repeat setoid_rewrite bind_ret_.
unfold allocate_declarations. unfold allocate_declaration. simpl.
repeat setoid_rewrite bind_ret_.
repeat setoid_rewrite bind_bind.
repeat setoid_rewrite bind_ret_.
unfold endo. unfold Endo_id. 
reflexivity.
Qed.


Lemma unfold_iter {E A B} (f : A -> itree E (A + B)) (x : A) :
  (ITree.iter f x) ≈ ITree.bind (f x) (fun lr => ITree.on_left lr l (Tau (ITree.iter f l))).
Proof.
  rewrite unfold_aloop_. reflexivity.
Qed.

(* Lemma eq_what : (Eqv.eqv (Name "entry") (Name "entry")) -> (if Eqv.eqv_dec_p (Name "entry") (Name "entry") then true else false) = true.
Proof.
pose Eqv.eqv (Name "entry") (Name "entry")
*)

Lemma eq_entry : (if Eqv.eqv_dec_p (Name "entry") (Name "entry") then true else false) = true.
Proof.
destruct Eqv.eqv_dec_p.
 + reflexivity.
 + contradict n. reflexivity.
Qed. 

(* Lemma empty_iter : 
ITree.iter
             (fun '(bid_from, bid_src) =>
              match
                (if if Eqv.eqv_dec_p (Name "entry") bid_src then true else false
                 then
                  Some
                    (tfmap (typ_to_dtyp [])
                       {|
                         blk_id := Name "entry";
                         blk_phis := [];
                         blk_code := [];
                         blk_term := TERM_Ret (TYPE_I 32, EXP_Integer 1%Z);
                         blk_comments := None
                       |})
                 else None)
              with
              | Some block_src =>
                  bd <-
                  ((dvs <- Util.map_monad (fun x : local_id * phi dtyp => translate exp_to_instr ⟦ x ⟧Φ (bid_from)) (blk_phis block_src);;
                    Util.map_monad (fun '(id, dv) => trigger (LocalWrite id dv)) dvs;; Ret tt);;
                   (Util.map_monad denote_instr (blk_code block_src);; Ret tt);; translate exp_to_instr ⟦ blk_term block_src ⟧t);;
                  match bd with
                  | inl bid_target => Ret (inl (bid_src, bid_target))
                  | inr dv => Ret (inr (inr dv))
                  end
              | None => Ret (inr (inl (bid_from, bid_src)))
              end) (Name "entry", Name "entry") ≈ Ret (inr (UVALUE_I32 (Int32.repr 1))) .
Proof.
setoid_rewrite unfold_iter.
simpl.
rewrite eq_entry. simpl. cbn.
repeat setoid_rewrite bind_ret_.
unfold exp_to_instr. simpl.
unfold denote_exp . simpl. rewrite typ_to_dtyp_equation. unfold coerce_integer_to_int. simpl.
repeat setoid_rewrite bind_ret_. rewrite unfold_translate . simpl. rewrite bind_ret_. rewrite bind_ret_.
reflexivity.
Qed.

Lemma test_lemma1 : ⟦ tfmap (typ_to_dtyp []) [{| blk_id := Name "entry"; blk_phis := []; blk_code := []; blk_term := TERM_Ret (TYPE_I 32, EXP_Integer 1%Z); blk_comments := None |}] ⟧bs (Name "entry", Name "entry") ≈ Ret (inr (UVALUE_I32 (Int32.repr 1))).
Proof.
cbn. 
unfold denote_ocfg. cbn. simpl. simpl_iter.
setoid_rewrite empty_iter.
reflexivity.
Qed.

Lemma test_lemma2 : r <-
        ⟦ [tfmap (typ_to_dtyp [])
             {|
               blk_id := Name "entry";
               blk_phis := [];
               blk_code := [];
               blk_term := TERM_Ret (TYPE_I 32, EXP_Integer 1%Z);
               blk_comments := None
             |}] ⟧bs (Name "entry", Name "entry");;
        match r with
        | inl bid => raise ("Can't find block in denote_cfg " ++ CeresSerialize.to_string (snd bid))
        | inr uv => Ret uv
        end ≈ Ret (UVALUE_I32 (Int32.repr 1)).
Proof. 
  rewrite test_lemma1. rewrite bind_ret_. reflexivity.
Qed.

Lemma test_lemma3 : translate instr_to_L0'
       (r <-
        ⟦ [tfmap (typ_to_dtyp [])
             {|
               blk_id := Name "entry";
               blk_phis := [];
               blk_code := [];
               blk_term := TERM_Ret (TYPE_I 32, EXP_Integer 1%Z);
               blk_comments := None
             |}] ⟧bs (Name "entry", Name "entry");;
        match r with
        | inl bid => raise ("Can't find block in denote_cfg " ++ CeresSerialize.to_string (snd bid))
        | inr uv => Ret uv
        end) ≈ Ret (UVALUE_I32 (Int32.repr 1)).
Proof.
  unfold instr_to_L0'.
  rewrite test_lemma2. cbn.
  rewrite unfold_translate. simpl.
  reflexivity.
Qed.

Lemma test_lemma4 : rv <-
     translate instr_to_L0'
       (r <-
        ⟦ [tfmap (typ_to_dtyp [])
             {|
               blk_id := Name "entry";
               blk_phis := [];
               blk_code := [];
               blk_term := TERM_Ret (TYPE_I 32, EXP_Integer 1%Z);
               blk_comments := None
             |}] ⟧bs (Name "entry", Name "entry");;
        match r with
        | inl bid => raise ("Can't find block in denote_cfg " ++ CeresSerialize.to_string (snd bid))
        | inr uv => Ret uv
        end);; trigger StackPop;; trigger MemPop;; Ret rv ≈ trigger StackPop;; trigger MemPop;; Ret (UVALUE_I32 (Int32.repr 1)).
Proof.
rewrite test_lemma3.
setoid_rewrite bind_ret_.
reflexivity.
Qed.

(* Lemma test_lemma5 : (fun args : list uvalue =>
       bs <-
       lift_err (fun x0 : list (local_id * uvalue) => Ret x0) match args with
                                                              | [] | _ => inr []
                                                              end;;
       trigger MemPush;;
       trigger (StackPush (map (fun '(k, v) => (k, v)) bs));;
       rv <-
       translate instr_to_L0'
         (r <-
          ⟦ [tfmap (typ_to_dtyp [])
               {|
                 blk_id := Name "entry";
                 blk_phis := [];
                 blk_code := [];
                 blk_term := TERM_Ret (TYPE_I 32, EXP_Integer 1%Z);
                 blk_comments := None
               |}] ⟧bs (Name "entry", Name "entry");;
          match r with
          | inl bid => raise ("Can't find block in denote_cfg " ++ CeresSerialize.to_string (snd bid))
          | inr uv => Ret uv
          end);; trigger StackPop;; trigger MemPop;; Ret rv) [] ≈ Ret (UVALUE_I32 (Int32.repr 1)). *)

Ltac pose_interp3_alloca m' a' A AE:=
  match goal with
  | [|-context[ℑs3 (trigger (Alloca ?t)) ?g ?l ?m]] =>
    pose proof (interp3_alloca
                  m t g l)
      as [m' [a' [A AE]]]
  end. *)

Locate resum.
Locate pat.

(* Lemma test2 : State.interp_state (interp_local_stack_h (handle_local (v:=uvalue))) (SemNotations.Ret1 [] 1) (nil, nil) = Ret tt. *)

(* Lemma test : interp_mcfg3  (trigger (Alloca DTYPE_Pointer);; Ret tt) [] ([],[]) empty_memory_stack ≈
 Ret (empty_memory_stack, (nil, nil, (nil, tt))) .
Proof.
unfold interp_mcfg3.
MCFGTactics.go.
rewrite interp_memory_trigger. cbn.
rewrite bind_bind. cbn.
unfold lift_pure_err, lift_err.
unfold allocate. cbn.
MCFGTactics.go.
unfold concrete_empty, make_empty_logical_block.
reflexivity.

setoid_rewrite interp_memory_ret  .
vred_E3.

setoid_rewrite interp_intrinsics_bind_trigger. cbn.
setoid_rewrite interp_intrinsics_ret. simpl.
unfold resum.
unfold ReSum_inr.
unfold resum.
unfold ReSum_inl.
unfold resum.
unfold ReSum_id.
unfold id_.
unfold Id_IFun.
simpl.
unfold cat, Cat_IFun. unfold inl_, inr_.
unfold Inr_sum1, Inl_sum1.
setoid_rewrite interp_global_bind_trigger. cbn.
setoid_rewrite interp_global_ret.
setoid_rewrite interp_local_stack_bind.
setoid_rewrite interp_local_stack_bind.
setoid_rewrite interp_local_stack_trigger. cbn.
unfold interp_local_stack. simpl. unfold interp_local_stack_h. simpl.

repeat setoid_rewrite interp_memory_bind  .
setoid_rewrite interp_memory_trigger. cbn. simpl. cbn. simpl.
repeat setoid_rewrite bind_ret_. 
setoid_rewrite interp_memory_ret.
repeat setoid_rewrite bind_ret_. simpl.

repeat setoid_rewrite interp_state_ret.
setoid_rewrite bind_ret_. cbn.
unfold interp_memory. simpl.
unfold interp_memory_h. simpl.

setoid_rewrite interp_memory_bind.


unfold ReSum_inr. cbn.


setoid_rewrite interp3_bind .
setoid_rewrite interp3_alloca.
pose (t := DTYPE_Pointer).
unfold non_void in H.
assert (non_void DTYPE_Pointer).
{
unfold non_void.
f_equal. 

}
assert (H_pointer : exists (m' : memory_stack) (a' : addr),
            allocate empty_memory_stack DTYPE_Pointer = inr (m', a') /\
            ℑs3 (trigger (Alloca DTYPE_Pointer)) [] ([], []) empty_memory_stack ≈
            ret (m', ([], ([] , DVALUE_Addr a')))). *)

Lemma denote_simpl : (denote_mcfg
              [(DVALUE_Addr (0%Z, 0%Z),
               ⟦ tfmap (typ_to_dtyp [])
                   {|
                     df_prototype :=
                       {|
                         dc_name := Name "main";
                         dc_type := TYPE_Function (TYPE_I 32) [];
                         dc_param_attrs := ([], []);
                         dc_linkage := None;
                         dc_visibility := None;
                         dc_dll_storage := None;
                         dc_cconv := None;
                         dc_attrs := [];
                         dc_section := None;
                         dc_align := None;
                         dc_gc := None
                       |};
                     df_args := [];
                     df_instrs :=
                       cfg_of_definition typ
                         {|
                           df_prototype :=
                             {|
                               dc_name := Name "main";
                               dc_type := TYPE_Function (TYPE_I 32) [];
                               dc_param_attrs := ([], []);
                               dc_linkage := None;
                               dc_visibility := None;
                               dc_dll_storage := None;
                               dc_cconv := None;
                               dc_attrs := [];
                               dc_section := None;
                               dc_align := None;
                               dc_gc := None
                             |};
                           df_args := [];
                           df_instrs :=
                             ({|
                                blk_id := Name "entry"; blk_phis := []; blk_code := []; blk_term := TERM_Ret (TYPE_I 32, EXP_Integer 1%Z); blk_comments := None
                              |}, [])
                         |}
                   |} ⟧f)] (DTYPE_I 32) (dvalue_to_uvalue (DVALUE_Addr (0%Z, 0%Z))) []) ≈ Ret (UVALUE_I32 (repr 1)).
Proof.
unfold denote_mcfg.
unfold mrec.
repeat setoid_rewrite bind_ret_. 
unfold lookup_defn. simpl.
unfold dvalue_eq_dec.
unfold dvalue_to_uvalue. simpl.



Theorem empty_th : ℑs3 e_test [] ([],[]) empty_memory_stack  ≈ Ret (empty_memory_stack, (nil, nil, (nil,  (UVALUE_I32 (repr 1))))).
Proof.
unfold e_test. unfold denote_vellvm.
rewrite empty_env.
unfold ℑs3. cbn.
MCFGTactics.go.
rewrite interp_memory_trigger. cbn. unfold lift_pure_err. simpl. cbn. setoid_rewrite bind_ret_. setoid_rewrite bind_ret_.
rewrite interp_memory_ret. setoid_rewrite bind_ret_.
rewrite interp_local_stack_ret.
rewrite interp_memory_ret. setoid_rewrite bind_ret_.
MCFGTactics.go.
unfold denote_mcfg. simpl.



rewrite ITree.Interp.RecursionFacts.mrec_as_interp.
rewrite unfold_interp. unfold _interp. simpl. unfold concretize_or_pick.

Import DenoteTactics.
setoid_rewrite bind_bind    .

unfold cfg_of_definition. simpl.
unfold address_one_function. simpl.
unfold denote_function. simpl.
unfold denote_cfg. simpl. cbn.
unfold endo. unfold Endo_id.
unfold ℑs3.
MCFGTactics.go.
repeat rewrite interp_memory_trigger. cbn.
rewrite bind_bind. cbn.
unfold lift_pure_err, lift_err.
unfold allocate. cbn.
MCFGTactics.go.
unfold interp_memory.
unfold interp_local_stack. cbn.
rewrite unfold_interp_state.
unfold _interp_state. cbn.
unfold interp_local_stack_h.
simpl.


auto.
setoid_rewrite interp3_bind_trigger .
pose_interp3_alloca.
setoid_rewrite bind_trigger.
setoid_rewrite interp1_ret. 
setoid_rewrite test_lemma4.
setoid_rewrite bind_ret_. rewrite bind_trigger. setoid_rewrite bind_trigger. cbn. setoid_rewrite test_lemma.
rewrite empty_iter.
setoid_rewrite unfold_iter.


unfold convert_types. unfold mcfg_of_tle. unfold mcfg_of_modul. simpl.
repeat setoid_rewrite bind_ret_.
unfold build_global_environment.
simpl. cbn.
repeat setoid_rewrite bind_ret_.
unfold denote_function. unfold denote_cfg.
simpl. cbn.
setoid_rewrite bind_vis. setoid_rewrite bind_vis. setoid_rewrite bind_vis. repeat setoid_rewrite bind_ret_. repeat setoid_rewrite bind_bind. repeat setoid_rewrite bind_ret_. cbn.
setoid_rewrite translate_ret. repeat setoid_rewrite bind_ret_.
unfold denote_ocfg. simpl. cbn. simpl.
give_up.
Admitted.



Definition empty_cfg : cfg dtyp :=
{|
  init := Anon 0%Z;
  blks := nil;
  args := nil;
|}.

Definition empty_dec : declaration dtyp :=
{|
  dc_name        := Anon 1%Z;
  dc_type        := (DTYPE_I 32%N) ;    (* INVARIANT: should be TYPE_Function (ret_t * args_t) *)
  dc_param_attrs := (nil, nil); (* ret_attrs * args_attrs *)
  dc_linkage     := None;
  dc_visibility  := None;
  dc_dll_storage := None;
  dc_cconv       := None;
  dc_attrs       := nil;
  dc_section     := None;
  dc_align       := None;
  dc_gc          := None;
|}.

Definition empty_def : definition dtyp (cfg dtyp) :=
{|
  df_prototype   := empty_dec;
  df_args        := nil;
  df_instrs      := empty_cfg;
|}.


Definition empty_fun : function_denotation :=
  denote_function empty_def.

 Definition empty_mcfg : itree L0 uvalue :=
  denote_mcfg [((DVALUE_I32 (repr 0)), empty_fun)] (DTYPE_I 32%N) (UVALUE_I32 (repr 0)) nil. 

Check dvalue_eq_dec (d1:=DVALUE_I32 (Int32.repr 0))
         (d2:=DVALUE_I32 (Int32.repr 0)).

Lemma equals : 
DVALUE_I32 (Int32.repr 0) = DVALUE_I32 (Int32.repr 0).
Proof.
reflexivity.
Qed.

Lemma test : (if
      if
       dvalue_eq_dec (d1:=DVALUE_I32 (Int32.repr 0))
         (d2:=DVALUE_I32 (Int32.repr 0))
      then true
      else false
     then Some empty_fun
     else None)  = Some empty_fun.
Proof.
  pose proof equals as Hequals.
  destruct dvalue_eq_dec as [Heq | Hneq].
    - reflexivity.
    - contradiction.
Qed.

Lemma fun_empty : empty_fun [] ≈ Ret (UVALUE_I32 (repr 0)).
Proof.
unfold empty_fun.
unfold denote_function. simpl.
give_up.
Admitted.
(* 
Definition dirty_tree {E:Type->Type} {T:Type} : itree (CallE +' ExternalCallE +' E) unit :=
  Ret tt.

Definition clean_tree {E:Type->Type} {T:Type}  : itree (ExternalCallE +' E) unit :=
  Ret tt.

(* The term "dirty_tree" has type "itree (CallE +' ExternalCallE) unit" while it is expected to have type
 "forall T : Type, CallE T -> itree (CallE +' ExternalCallE +' ?E2) T". *)


Definition empty_conv {E:Type->Type} : forall T : Type, CallE T -> itree (ExternalCallE +' E) T :=
fun T call => clean_tree.


Definition easy_rec :=
        @mrec CallE (ExternalCallE +' _) dirty_tree unit.
 *)

             


Lemma test1 : denote_ocfg [] (Anon 0%Z, Anon 0%Z) ≈ Ret (inl (Anon 0%Z, Anon 0%Z)).
Proof.
setoid_rewrite denote_ocfg_nil.
reflexivity.
Qed.

Theorem empty_th2 : empty_mcfg ≈ Ret (UVALUE_I32 (repr 0)).
Proof.
unfold empty_mcfg.
unfold denote_mcfg.
simpl.
unfold concretize_or_pick. simpl.
unfold mrec. simpl.
repeat setoid_rewrite bind_ret_. simpl.
pose proof equals as Hequals.
rewrite test. setoid_rewrite unfold_interp_mrec.
unfold _interp_mrec. cbn. simpl. repeat setoid_rewrite bind_ret_.  setoid_rewrite unfold_interp_mrec. unfold _interp_mrec. cbn. setoid_rewrite unfold_interp_mrec. unfold _interp_mrec. cbn. setoid_rewrite test1.
unfold denote_ocfg. simpl. unfold iter.
 setoid_rewrite bind_ret_r_.



 unfold empty_fun. unfold empty_def. unfold denote_function. simpl. repeat setoid_rewrite bind_ret_. simpl.
unfold mrecursive. simpl.
apply Proper_interp_mrec .

unfold dvalue_to_uvalue.
rewrite interp_mrecursive.