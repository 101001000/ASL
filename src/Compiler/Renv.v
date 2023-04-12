From Coq    Require Import String BinNat.
From Vellvm Require Import Syntax Semantics Utils.AListFacts.
From ASL    Require Import Semantics.

(* Get the Z value of a variable name X in the memory *)
Definition get_val (g: global_env) (l: local_env) (m: memory_stack) (x: string) : option int32 :=
  let addr := FMapAList.alist_find (Name x) l
  in match addr with 
    | Some (UVALUE_Addr ptr) =>
        let val := read m ptr (DTYPE_I 32%N) in 
        match val with
          | inl _ => None
          | inr v => match v with
                      | UVALUE_I32 i => Some i
                      | _ => None
                     end
        end
    | _ => None
  end.

Definition Renv (env_asl : env) (g_llvm : global_env) (l_llvm : local_env) (m_llvm : memory_stack) : Prop :=
forall k v, alist_In k env_asl v <-> (get_val g_llvm l_llvm m_llvm k) = Some v. 

