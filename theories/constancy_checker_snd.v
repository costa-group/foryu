Require Import FORYU.state.
Require Import FORYU.program.
Require Import FORYU.semantics.
Require Import FORYU.constancy.
Require Import FORYU.constancy_snd.

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.

Module Constancy_checker_snd (D: DIALECT).

  (* [ConstSndD] is projected *out of* [ConstD] (not independently
  instantiated) so that everything below shares one single
  [SmallStep(D)]/[CFGProg(D)] lineage -- see the comment on
  [Constancy]'s own header in constancy.v for why that matters. *)
  Module ConstD := Constancy(D).
  Module ConstSndD := ConstD.ConstSndD.

  Module SmallStepD := ConstD.SmallStepD.
  Module StateD := ConstD.StateD.
  Module CallStackD := ConstD.CallStackD.
  Module StackFrameD := ConstD.StackFrameD.
  Module LocalsD := ConstD.LocalsD.
  Module CFGProgD := ConstD.CFGProgD.
  Module CFGFunD := ConstD.CFGFunD.
  Module BlockD := ConstD.BlockD.
  Module PhiInfoD := ConstD.PhiInfoD.
  Module InstrD := ConstD.InstrD.
  Module ExitInfoD := ConstD.ExitInfoD.
  Module SimpleExprD := ConstD.SimpleExprD.

  Import SmallStepD.
  Import StateD.
  Import CallStackD.
  Import StackFrameD.
  Import LocalsD.
  Import CFGProgD.
  Import CFGFunD.
  Import BlockD.
  Import PhiInfoD.
  Import InstrD.
  Import ExitInfoD.
  Import SimpleExprD.

  (* Soundness of the boolean constancy checker: whatever a
  checker-validated result [r] claims about a program point is really
  true of it, in the sense of [ConstSndD.const_at_pc] -- the same
  ground-truth relation whose own semantic soundness (w.r.t. actual
  program execution) is proven in constancy_snd.v. Composing the two
  theorems is what ultimately justifies using [r] (as produced by
  whatever external analysis constructs it) to inform real program
  transformations: [check_const_program p r = true] plus
  [VarMap.find v pp_info = Some c] at a reachable program point implies
  the value of [v] there is actually, always, [c]. *)
  Theorem check_const_program_snd :
    forall (p: CFGProgD.t) (r: ConstD.prog_const_info_t),
      ConstD.check_const_program p r = true ->
      forall (fn: FuncName.t) (f: CFGFunD.t) (f_info: ConstD.func_const_info_t)
             (bid: BlockID.t) (b: BlockD.t) (b_info: ConstD.block_const_info_t)
             (pc: nat) (pp_info: ConstD.pp_const_info_t) (v: VarID.t) (c: D.value_t),
        CFGProgD.get_func p fn = Some f ->
        r fn = Some f_info ->
        CFGProgD.get_block p fn bid = Some b ->
        f_info bid = Some b_info ->
        List.nth_error b_info pc = Some pp_info ->
        VarMap.find v pp_info = Some c ->
        ConstSndD.const_at_pc p fn bid pc v c.
  Admitted.

End Constancy_checker_snd.
