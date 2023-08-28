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

Definition gen_body_code (p : AST.stmt) : code dtyp :=
  match p with
  | Skip => nil
  | Assign x v => match v with 
                  | Lit n => [(IId (Anon 0%Z), (INSTR_Op (EXP_Integer (Int32.unsigned n))))]
                  | Var x => [(IId (Anon 0%Z), (INSTR_Load false (DTYPE_I 32%N) (DTYPE_Pointer, (EXP_Ident (ID_Local (Name x)))) None))]
  end ++ [(IVoid 0%Z, (INSTR_Store false ((DTYPE_I 32%N), (EXP_Ident (ID_Local (Anon 0%Z)))) (DTYPE_Pointer, (EXP_Ident (ID_Local (Name x)))) None))]
  end.


Fixpoint compile_aux (p : AST.prog) : code dtyp :=
  match p with
  | nil => nil
  | x :: t => (gen_body_code x) ++ (compile_aux t)
  end.

Definition compile (p : AST.prog) : code dtyp :=
  compile_aux p.


Definition extract_z_instr_id (ins:instr_id) : Z :=
  match ins with
  | IId r => match r with
             | Anon z => z
             | _ => -1%Z
             end
  | _ => -1%Z
  end.

Definition extract_z_ident (id:ident) : Z :=
  match id with
  | ID_Local r => match r with
                  | Anon z => z
                  | _ => -1%Z
                  end
  | _ => -1%Z
  end.


Fixpoint replace_exp (e : exp dtyp) (map : FMapAList.alist Z Z) :=
  match e with
  | EXP_Ident id => match FMapAList.alist_find (extract_z_ident id) map with
                    | Some v => EXP_Ident (ID_Local (Anon v))
                    | None => e
                    end
  | OP_IBinop v1 v2 e1 e2 => OP_IBinop v1 v2 (replace_exp e1 map) (replace_exp e2 map)
  | _ => e
  end.



Definition replace_inst (ib : instr dtyp) (map : FMapAList.alist Z Z) : instr dtyp :=
  match ib with
  | INSTR_Op e => INSTR_Op (replace_exp e map)
  | INSTR_Store v (t, e1) (t2, e2) a => INSTR_Store v (t, (replace_exp e1 map)) (t2, e2) a
  | _ => ib
  end.


Definition replace_id (id: instr_id) (map : FMapAList.alist Z Z) : instr_id :=
  match id with
  | IId r => match r with
             | Anon z => match FMapAList.alist_find (extract_z_instr_id id) map with
                         | Some v => IId (Anon v)
                         | None => id
                         end
             | _ => id
             end
  | _ => id
  end.


Fixpoint ssa (input : code dtyp) (map : FMapAList.alist Z Z) (c : Z): code dtyp :=
  match input with
  | nil => nil
  | h :: t => let '(id, ib) := h in
              let zid := extract_z_instr_id id in
              let ib' := replace_inst ib map in
              let map' := if (zid =? (-1%Z))%Z then map else (match FMapAList.alist_find zid map with | Some v => FMapAList.alist_add zid c map | None => FMapAList.alist_add zid zid map end) in
              let c'   := if (zid =? (-1%Z))%Z then c else (match FMapAList.alist_find zid map with | Some v => (c + 1)%Z | None => c end) in
              let id'  := replace_id id map' in
                (id', ib') :: (ssa t map' c')
  end.



Compute ssa (compile ([Assign "x" (Lit (Int32.repr 5%Z));Assign "y" (Lit (Int32.repr 3%Z));Assign "x" (Var "x")])) ([]) (1%Z).






