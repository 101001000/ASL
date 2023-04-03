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

Definition empty_block : block dtyp :=
    {|
      blk_id    := (Anon 0%Z);
      blk_phis  := nil;
      blk_code  := nil;
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
   empty_cfg empty_block.

  

