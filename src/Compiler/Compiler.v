From Coq    Require Import String BinNat List ZArith.
From ASL    Require Import AST.
From Vellvm Require Import Syntax Semantics.

Import ListNotations.

Open Scope list_scope.

(* First we need to extract all the variables initialized inside an ASL program *)
Section Allocations.

  Fixpoint eqb s1 s2 : bool :=
   match s1, s2 with
   | EmptyString, EmptyString => true
   | String c1 s1', String c2 s2' => Ascii.eqb c1 c2 && eqb s1' s2'
   | _,_ => false
   end.

  Fixpoint is_present (s : string) (l : list string) (b : bool) : bool :=
    match l with
    | h::tail => is_present s tail (orb b (eqb h s))
    | [] => b
    end.

  Fixpoint extract_vars (p : AST.stmt) (l : list string) : list string :=
    match p with
    | Skip => l
    | Assign x e => if (is_present x l false) then l else (x::l) 
    end.

  Definition gen_alloc_instr (x:string) : instr_id * instr dtyp :=
    (IId (Name x), (INSTR_Alloca (DTYPE_I 32%N) None None)).

  Definition gen_alloc_code (p : AST.stmt) : code dtyp :=
    let var_list := extract_vars p nil in
      map gen_alloc_instr var_list.

End Allocations.



(* Given an ASL program, generate the instructions assuming the variables have been previously allocated *)
Definition gen_body_code (p : AST.stmt) : code dtyp :=
  match p with
  | Skip => nil
  | Assign x v => match v with 
                  | Lit n => [(IVoid 0%Z, (INSTR_Store false ((DTYPE_I 32%N), (EXP_Integer (Int32.unsigned n))) (DTYPE_Pointer, (EXP_Ident (ID_Local (Name x)))) None))]
                  end
  end.

(* This function generates a cfg without args, with just one code block labeled as 0 which always return 1 and with code "c" *)
Definition generate_cfg (c : code dtyp) : cfg dtyp := 
  {| init := (Anon 0%Z);
     blks := [{|
                blk_id    := (Anon 0%Z);
                blk_phis  := nil;
                blk_code  := c;
                blk_term  := TERM_Ret ((DTYPE_I 32%N), (EXP_Integer (1)%Z));
                blk_comments := None
              |} ];
     args := nil |} .


(* Convert a program in ASL AST form, into a LLVM AST form *)
Definition compile (p : AST.stmt) : cfg dtyp :=
  let alloc_code := gen_alloc_code p in
  let body_code  := gen_body_code  p in
  generate_cfg (alloc_code ++ body_code).

   






