From Vellvm Require Import
Semantics.Denotation Semantics.TopLevel Syntax.LLVMAst Utilities.

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

Definition code := list (instr_id * instr typ).

Definition gen_block_body (c: code) : block typ := 
{| blk_id := (Anon 0%Z);
   blk_phis := [];
   blk_code := c;
   blk_term := TERM_Ret ((TYPE_I 32%N), (EXP_Ident (ID_Local (Anon 1%Z))));
   blk_comments := None
|}.

Local Open Scope lazy_bool_scope.

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

  

  

Definition test_program :=
  Seq (Assign "x" (Lit 1)) (Assign "y" (Lit 2)).

Compute(extract_vars test_program []).

Definition gen_global {FnBody: Set}  (x:string) : toplevel_entity _ FnBody :=
TLE_Global {|
  g_ident        := Name x;
  g_typ          := (TYPE_I 32%N) ; (* globals are always pointers *)
  g_constant     := false ;
  g_exp          := (Some (EXP_Integer (0)%Z));
  g_linkage      := None ;
  g_visibility   := None ;
  g_dll_storage  := None ;
  g_thread_local := None ;
  g_unnamed_addr := false ;
  g_addrspace    := None ;
  g_externally_initialized:= false ;
  g_section      := None ;
  g_align        := None;
|}.


Fixpoint gen_globals {FnBody: Set} (l : list string) (tle : list (toplevel_entity _ FnBody)) : list (toplevel_entity _ FnBody) :=
  match l with
  | h::tail => (gen_global h)::(gen_globals tail tle)
  | [] => tle
  end.
  


Definition gen_code_e (c:int) (e : expr) : code :=
  match e with
  | Lit n => [(IId (Anon c), (INSTR_Op (OP_IBinop (LLVMAst.Add false false) (TYPE_I 32%N) (EXP_Integer (n)) (EXP_Integer 0%Z))))]
  | Var x => [(IId (Anon c), (INSTR_Load false (TYPE_I 32%N) ((TYPE_Pointer (TYPE_I 32%N)), EXP_Ident (ID_Global (Name x))) None))]
  end.

Fixpoint gen_code (c:int) (p : Ast.stmt) : code :=
  match p with
  | Skip => nil
  | Assign x e => app (gen_code_e c e) [(IVoid 0%Z, (INSTR_Store false ((TYPE_I 32%N), (EXP_Ident (ID_Local (Anon c)))) ((TYPE_Pointer (TYPE_I 32%N)), (EXP_Ident (ID_Global (Name x)))) None))]
  | Seq s1 s2 => app (gen_code c s1) (gen_code (Z.add c 1%Z) s2)
  end.


Definition gen_main (p : Ast.stmt) := 
LLVMAst.TLE_Definition {|
  df_prototype := {|dc_name := (Name "main");
                    dc_type := (TYPE_Function (TYPE_I 32%N) nil);
                    dc_param_attrs := (nil, nil);
                    dc_linkage := None;
                    dc_visibility := None;
                    dc_dll_storage := None;
                    dc_cconv := None;
                    dc_attrs := nil;
                    dc_section := None;
                    dc_align := None;
                    dc_gc := None|};
  df_args := nil;
  df_instrs := (gen_block_body (gen_code 1%Z p), nil (A:=block typ))
                |}.


Check(gen_main).


Definition compile (p : Ast.stmt) : list (toplevel_entity typ (LLVMAst.block typ * list (LLVMAst.block typ))) :=

  let vars := extract_vars p [] in
  app (gen_globals (FnBody:= block typ * list (block typ)) vars []) [gen_main p].
  

