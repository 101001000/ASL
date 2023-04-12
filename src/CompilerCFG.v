From Vellvm Require Import
Semantics Syntax Theory Utilities.

From Coq Require Import
 ZArith Strings.String.

From Coq Require Import List String Ascii ZArith.

From ASL Require Import
  Ast.

From ExtLib Require Import
     Data.List.

Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.



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

Fixpoint extract_vars (p : Ast.stmt) (l : list string) : list string :=
  match p with
  | Skip => l
  | Assign x e => if (is_present x l false) then l else (x::l) 
  | Seq s1 s2 => let l1 := (extract_vars s1 l) in (extract_vars s2 l1)
  end.


Definition gen_alloc (x:string) : instr_id * instr dtyp :=
  (IId (Name x), (INSTR_Alloca (DTYPE_I 32%N) None None)).

Definition gen_allocs (p : Ast.stmt) : code dtyp :=
  let var_list := extract_vars p [] in
    map gen_alloc var_list.
  


Definition gen_code (p : Ast.stmt) : code dtyp :=
  match p with
  | Skip => nil
  | Assign x v => match v with 
                  | Lit n => [(IVoid 0%Z, (INSTR_Store false ((DTYPE_I 32%N), (EXP_Integer (n))) (DTYPE_Pointer, (EXP_Ident (ID_Local (Name x)))) None))]
                  end
  | _ => nil
  end.



Definition empty_block (c : code dtyp) : block dtyp :=
    {|
      blk_id    := (Anon 0%Z);
      blk_phis  := nil;
      blk_code  := c;
      blk_term  := TERM_Ret ((DTYPE_I 32%N), (EXP_Integer (1)%Z));
      blk_comments := None
    |}.

Definition empty_cfg (b : block dtyp) : cfg dtyp := 
                  {|
                    init := (Anon 0%Z);
                    blks := [b];
                    args := nil;
                  |}.


Definition compile_cfg (p : Ast.stmt) : cfg dtyp :=
   empty_cfg (empty_block (app (gen_allocs p) (gen_code p))).

  

