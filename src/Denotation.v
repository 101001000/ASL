From ASL Require Import
  Ast.

From Coq Require Import
     ZArith
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.StateFacts.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

Variant ImpState : Type -> Type :=
| GetVar (x : var) : ImpState Z
| SetVar (x : var) (v : Z) : ImpState unit.

(*ASL AS A REALLY SIMPLE SUBSET OF THE IMP LANGUAGE PROPOSED IN THE iTree REPO TUTORIAL*)

Section Denote.

  Context {eff : Type -> Type}.
  Context {HasImpState : ImpState -< eff}.

  Fixpoint denote_expr (e : expr) : itree eff Z :=
    match e with
    | Var v     => trigger (GetVar v)
    | Lit n     => ret n
    end.

  Fixpoint denote_asl (s : stmt) : itree eff unit :=
    match s with
    | Assign x e =>  v <- denote_expr e ;; trigger (SetVar x v)
    | Seq a b    =>  denote_asl a ;; denote_asl b
    | Skip => ret tt
    end.

End Denote.

Instance RelDec_string : RelDec (@eq string) :=
  { rel_dec := fun s1 s2 => if string_dec s1 s2 then true else false}.

#[global]
Instance RelDec_string_Correct: RelDec_Correct RelDec_string.
Proof.
  constructor; intros x y.
  split.
  - unfold rel_dec; simpl.
    destruct (string_dec x y) eqn:EQ; [intros _; apply string_dec_sound; assumption | intros abs; inversion abs].
  - intros EQ; apply string_dec_sound in EQ; unfold rel_dec; simpl; rewrite EQ; reflexivity.
Qed.

Definition handle_ImpState {E: Type -> Type} `{mapE var 0%Z -< E}: ImpState ~> itree E :=
  fun _ e =>
    match e with
    | GetVar x => lookup_def x
    | SetVar x v => insert x v
    end.


Definition env := alist var Z.

Definition interp_asl  {E A} (t : itree (ImpState +' E) A) : stateT env (itree E) A :=
  let t' := interp (bimap handle_ImpState (id_ E)) t in
  interp_map t'.


Section InterpImpProperties.

  Context {E': Type -> Type}.
  Notation E := (ImpState +' E').

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

End InterpImpProperties.




