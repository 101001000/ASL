From Coq    Require Import Strings.String BinNat List ZArith ListSet.
From Lang   Require Import AST Theory.
From Vellvm Require Import Syntax Semantics.
From ExtLib Require Import Core.RelDec Data.String Data.Map.FMapAList . 

Import ListNotations.

Open Scope list_scope.




(* First we need to extract all the variables initialized inside an ASL program *)
Section Allocations.


(* (*   Fixpoint gen_alloc_instrs (p : AST.stmt) (l : alist (instr_id * instr dtyp) unit) : alist (instr_id * instr dtyp) unit :=
    match p with
    | Skip => l
    | Seq s1 s2 => fold_alist alist_add (gen_alloc_instrs s2 nil) (gen_alloc_instrs s1 nil)
    | Assign x e => alist_add (IId (Name x), (INSTR_Alloca (DTYPE_I 32%N) None None)) tt l 
    end.
 *)
   Fixpoint extract_vars (p : AST.stmt) (l : alist string unit) : alist string unit :=
    match p with
    | Skip => l
    | Seq s1 s2 => fold_alist alist_add (extract_vars s2 nil) (extract_vars s1 nil)
    | Assign x e => l 
    end.

  Definition gen_alloc_instr (pair : (string * unit)): instr_id * instr dtyp :=
    (IId (Name (fst pair)), (INSTR_Alloca (DTYPE_I 32%N) None None)).

  Definition gen_alloc_code (p : AST.stmt) : code dtyp :=
    let var_list := extract_vars p nil in
      map gen_alloc_instr var_list.

  Fixpoint gen_decs_code (d : AST.decs) : code dtyp :=
    match d with
    | Dec x => [gen_alloc_instr (x, tt)]
    | DecSeq d1 d2 => gen_decs_code d1 ++ gen_decs_code d2
    end. *)

  

End Allocations.


Fixpoint compile_decs_s (ds:list dec) :=
match ds with
  | nil => nil
  | h :: t => match h with | Var x => [(LLVMAst.IId (LLVMAst.Name x), LLVMAst.INSTR_Alloca (TYPE_I 32) None None) ; (IVoid 0%Z, (INSTR_Store false ((TYPE_I 32%N), (EXP_Integer (Int32.unsigned (Int32.repr 0%Z)))) (TYPE_Pointer (TYPE_I 32), (EXP_Ident (ID_Local (Name x)))) None)) ] ++ (compile_decs_s t) end
end.

Fixpoint compile_decs (ds:list dec) :=
match ds with
  | nil => nil
  | h :: t => match h with | Var x => [(LLVMAst.IId (LLVMAst.Name x), LLVMAst.INSTR_Alloca (DTYPE_I 32) None None) ; (IVoid 0%Z, (INSTR_Store false ((DTYPE_I 32%N), (EXP_Integer (Int32.unsigned (Int32.repr 0%Z)))) (DTYPE_Pointer, (EXP_Ident (ID_Local (Name x)))) None)) ] ++ (compile_decs t) end
end.

Definition compile_stmt_s (s : stmt) : code typ :=
  match s with
  | Skip => nil
  | Assign x v => match v with 
                  | Lit n => [(IVoid 0%Z, (INSTR_Store false ((TYPE_I 32%N), (EXP_Integer (Int32.unsigned n))) (TYPE_Pointer (TYPE_I 32), (EXP_Ident (ID_Local (Name x)))) None))]
                  end
  end.

Fixpoint compile_stmts_s (ss : list stmt) : code typ :=
  match ss with
  | nil => []
  | h :: t => (compile_stmt_s h) ++ (compile_stmts_s t)
  end.

Definition compile_stmt (s : stmt) : code dtyp :=
  match s with
  | Skip => nil
  | Assign x v => match v with 
                  | Lit n => [(IVoid 0%Z, (INSTR_Store false ((DTYPE_I 32%N), (EXP_Integer (Int32.unsigned n))) (DTYPE_Pointer, (EXP_Ident (ID_Local (Name x)))) None))]
                  end
  end.

Fixpoint compile_stmts (ss : list stmt) : code dtyp :=
  match ss with
  | nil => []
  | h :: t => (compile_stmt h) ++ (compile_stmts t)
  end.


Definition compile (p : AST.prog) : code typ :=
  match p with
  | Prog ds ss => (compile_decs_s ds) ++ (compile_stmts_s ss)
  end.

(* Lemma convert_typ_code_cons: forall a (b : code typ) env, (convert_typ env (a :: b) = convert_typ env a ++ convert_typ env b)%list.
Proof.
  induction a as [| [] a IH]; cbn; intros; auto.
  rewrite IH; reflexivity.
Qed.
 *)

Lemma cons_app_singleton : forall (A : Type) (h : A) (t : list A),
  h :: t = [h] ++ t.
Proof.
  reflexivity.
Qed.


Lemma compile_decs_cons_app_singleton : forall t h,
compile_decs (h :: t) = compile_decs [h] ++ compile_decs t.
Proof.
intros.
unfold compile_decs.
destruct h.
reflexivity.
Qed.

Lemma compile_decs_s_cons_app_singleton : forall t h,
compile_decs_s (h :: t) = compile_decs_s [h] ++ compile_decs_s t.
Proof.
intros.
unfold compile_decs_s.
destruct h.
reflexivity.
Qed.

Lemma convert_typ_decs_singleton : forall a,
convert_typ [] (compile_decs_s [a]) = compile_decs [a].
Proof.
intros.
destruct a.
unfold convert_typ.
cbn.
repeat rewrite TypToDtyp.typ_to_dtyp_equation.
reflexivity.
Qed.

Lemma convert_typ_decs: forall ds,
TypToDtyp.convert_typ [] (compile_decs_s ds) = (compile_decs ds).
Proof.
induction ds.
+ simpl.
  unfold convert_typ.
  auto.
+ rewrite compile_decs_s_cons_app_singleton.
  symmetry.
  rewrite compile_decs_cons_app_singleton.
  rewrite TypToDtyp.convert_typ_code_app.
  rewrite convert_typ_decs_singleton.
  rewrite IHds.
  reflexivity.
Qed.


Lemma compile_stmts_cons_app_singleton : forall t h,
compile_stmts (h :: t) = compile_stmts [h] ++ compile_stmts t.
Proof.
intros.
unfold compile_stmts.
destruct h; simpl.
+ destruct e.
  reflexivity.
+ reflexivity.
Qed.

Lemma compile_stmts_s_cons_app_singleton : forall t h,
compile_stmts_s (h :: t) = compile_stmts_s [h] ++ compile_stmts_s t.
Proof.
intros.
unfold compile_stmts_s.
destruct h; simpl.
+ destruct e.
  reflexivity.
+ reflexivity.
Qed.

Lemma convert_typ_stmts_singleton : forall a,
convert_typ [] (compile_stmts_s [a]) = compile_stmts [a].
Proof.
intros.
destruct a.
+ simpl.
  destruct e.
  unfold convert_typ.
  cbn.
  repeat rewrite TypToDtyp.typ_to_dtyp_equation.
  reflexivity.
+ simpl.
  unfold convert_typ.
  cbn.
  reflexivity.
Qed.

Lemma convert_typ_stmts: forall ds,
TypToDtyp.convert_typ [] (compile_stmts_s ds) = (compile_stmts ds).
Proof.
induction ds.
+ simpl.
  unfold convert_typ.
  auto.
+ rewrite compile_stmts_s_cons_app_singleton.
  symmetry.
  rewrite compile_stmts_cons_app_singleton.
  rewrite TypToDtyp.convert_typ_code_app.
  rewrite convert_typ_stmts_singleton.
  rewrite IHds.
  reflexivity.
Qed.

Definition well_formed (ds:list dec) (ss:list stmt) : Prop :=
forall x e,
(In (Var x) ds <-> In (Assign x e) ss) /\
((~ In (Var x) ds) <-> (~ In (Assign x e) ss)) /\
((count_occ dec_dec ds (Var x)) < 2)%nat.

Definition well_formed_prog p :=
match p with
| Prog ds ss => well_formed ds ss
end.


