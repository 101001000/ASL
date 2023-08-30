From Coq    Require Import Strings.String BinNat List ZArith ListSet.
From Lang   Require Import AST.
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


Fixpoint compile_decs (ds:list dec) :=
match ds with
  | nil => nil
  | h :: t => match h with | Var x => [(LLVMAst.IId (LLVMAst.Name x), LLVMAst.INSTR_Alloca (DynamicTypes.DTYPE_I 32) None None) ; (IVoid 0%Z, (INSTR_Store false ((DTYPE_I 32%N), (EXP_Integer (Int32.unsigned (Int32.repr 0%Z)))) (DTYPE_Pointer, (EXP_Ident (ID_Local (Name x)))) None)) ] ++ (compile_decs t) end
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

Definition compile (p : AST.prog) : code dtyp :=
  match p with
  | Prog ds ss => (compile_decs ds) ++ (compile_stmts ss)
  end.






