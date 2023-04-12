From ASL         Require Import Semantics AST.
From ASLCompiler Require Import Compiler Renv.
From Vellvm      Require Import Semantics. 
From ITree       Require Import ITree ITreeFacts. 

Import SemNotations.

Definition eutt_inv (r1 : (env * unit)) (r2 : memory_stack * (local_env * (global_env * uvalue))) : Prop :=
let asl_env := fst r1 in
let m_llvm := fst r2 in
let l_llvm := fst (snd r2) in
let g_llvm := fst (snd (snd r2)) in
  Renv asl_env g_llvm l_llvm m_llvm.

Definition bisimilar (t1 : itree (State +' CallE +' PickE +' UBE +' DebugE +' FailureE) unit) (t2 : itree (instr_E) uvalue)  :=
  forall g_llvm l_llvm m_llvm g_asl,
    Renv g_asl g_llvm l_llvm m_llvm ->
      eutt eutt_inv
       (interp_asl t1 g_asl)
       (ℑ3 t2 g_llvm l_llvm m_llvm).

Theorem compiler_correct (s:stmt) :
  bisimilar (denote_asl s) (denote_cfg (compile s)).
Proof.
  give_up.
Admitted.