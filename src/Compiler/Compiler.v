From Coq    Require Import Strings.String BinNat List ZArith ListSet.
From ASL    Require Import AST.
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



(* (* Given an ASL program, generate the instructions assuming the variables have been previously allocated *)
Fixpoint gen_body_code (p : AST.stmt) : code dtyp :=
  match p with
  | Skip => nil
  | Seq s1 s2 => gen_body_code s1 ++ gen_body_code s2
  | Assign x v => match v with 
                  | Lit n => [(IVoid 0%Z, (INSTR_Store false ((DTYPE_I 32%N), (EXP_Integer (Int32.unsigned n))) (DTYPE_Pointer, (EXP_Ident (ID_Local (Name x)))) None))]
                  end
  end.

(* Convert a program in ASL AST form, into a LLVM AST form *)
Definition compile_body (p : AST.stmt) : code dtyp :=
  let alloc_code := gen_alloc_code p in
  let body_code  := gen_body_code  p in
  alloc_code ++ body_code.


Fixpoint compile_prog (p : AST.prog) : code dtyp :=
  match p with
  | Prog d s => gen_decs_code d ++ gen_body_code s
  end.



Definition sub  (k : string) (v : unit) (m : alist string unit) :=
match (alist_find k m) with
  | Some _ => alist_remove k m
  | None => m
end.

Definition alist_sub (m1 m2 : alist string unit) : alist string unit :=
fold_alist sub m1 m2.
 *)

Fixpoint gen_body_code (p : AST.stmt) : code dtyp :=
  match p with
  | Skip => nil
  | Assign x v => match v with 
                  | Lit n => [(IVoid 0%Z, (INSTR_Store false ((DTYPE_I 32%N), (EXP_Integer (Int32.unsigned n))) (DTYPE_Pointer, (EXP_Ident (ID_Local (Name x)))) None))]
                  end
  end.


Fixpoint compile (p : AST.prog) : code dtyp :=
  match p with
  | nil => nil
  | x :: t => (gen_body_code x) ++ (compile t)
  end.






