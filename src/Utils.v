From Vellvm Require Import
  Numeric.Integers Handlers Syntax Semantics.

From Coq Require Import
  String ZArith.

Require Import ExtLib.Structures.Maps.

(*Get the Z value of a variable name X in the memory*)
Definition get_val (g: global_env) (l: local_env) (m: memory_stack) (x: string) : option Z :=
  let addr := FMapAList.alist_find (Name x) l
  in match addr with 
    | Some (UVALUE_Addr ptr) =>
        let val := read m ptr (DTYPE_I 32%N) in 
        match val with
          | inl _ => None
          | inr v => match v with
                      | UVALUE_I32 i => Some (Int32.unsigned (i))
                      | _ => None
                     end
        end
    | _ => None
  end.