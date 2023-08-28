From Coq    Require Import String ZArith Morphisms.
From Vellvm Require Import Semantics.DynamicValues.
From ITree  Require Import ITree ITreeFacts Events.MapDefault Events.StateFacts.
From ASL    Require Import AST.
From ExtLib Require Import Structures.Monad Data.Map.FMapAList Data.String.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope list_scope.

(* This is a trimmed down version of the Imp denotational semantics of the iTree tutorial *)

Variant State : Type -> Type :=
| SetVar (x : string) (v : int32) : State unit
| GetVar (x : string)             : State int32.

(* We model the env state as a map of string-int32*)
Definition env := alist string int32.

Section Denote.

  Context {eff : Type -> Type}.
  Context {HasState : State -< eff}.

  Fixpoint denote_expr (e : expr) : itree eff int32 :=
    match e with
    | Lit n     => ret n
    | Var x     => trigger (GetVar x)
    end.

  Fixpoint denote_asl (s : stmt) : itree eff unit :=
    match s with
    | Assign x e =>  v <- denote_expr e ;; trigger (SetVar x v)
    | Skip => ret tt
    end.

  Fixpoint denote_prog (p : prog) : itree eff unit :=
    match p with
      | nil => ret tt
      | h :: t => denote_asl h ;; denote_prog t
    end.

Fixpoint denote_decs (ds : decs) : itree eff unit :=
  match ds with
    | nil => ret tt
    | h :: t => match h with | DVar x => trigger (SetVar x (Int32.repr 0%Z)) end ;; denote_decs t
end.




End Denote.

Section Interpretation.

  Definition handle_State {E: Type -> Type} `{mapE string (Int32.repr 0%Z) -< E}: State ~> itree E :=
  fun _ e => match e with
             | SetVar x v => insert x v
             | GetVar x => lookup_def x
             end.

  Definition interp_asl  {E A} (t : itree (State +' E) A) : stateT env (itree E) A :=
    let t' := interp (bimap handle_State (id_ E)) t in
    interp_map t'.

End Interpretation.

Section InterpretationProperties.

  Context {E': Type -> Type}.
  Notation E := (State +' E').

  (** This interpreter is compatible with the equivalence-up-to-tau. *)
  Global Instance eutt_interp_imp {R}:
    Proper (@eutt E R R eq ==> eq ==> @eutt E' (prod (env) R) (prod _ R) eq)
           interp_asl.
  Proof.
    repeat intro.
    unfold interp_asl.
    unfold interp_map.
    rewrite H0. eapply eutt_interp_state_eq; auto.
    rewrite H. reflexivity.
  Qed.

  (** [interp_imp] commutes with [bind]. *)
  Lemma interp_imp_bind: forall {R S} (t: itree E R) (k: R -> itree E S) (g : env),
      (interp_asl (ITree.bind t k) g)
    ≅ (ITree.bind (interp_asl t g) (fun '(g',  x) => interp_asl (k x) g')).
  Proof.
    intros.
    unfold interp_asl.
    unfold interp_map.
    repeat rewrite interp_bind.
    repeat rewrite interp_state_bind.
    apply eqit_bind; [ reflexivity | ].
    red. intros.
    destruct a as [g'  x].
    simpl.
    reflexivity.
  Qed.



End InterpretationProperties.