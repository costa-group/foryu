Require Import FORYU.state.
Require Import FORYU.program.
Require Import FORYU.semantics.

From Stdlib Require Import OrdersAlt.
From Stdlib Require Import FSets.FMapAVL.
From Stdlib Require Import List.

(* The representation of constancy information, shared by the
specification of valid constancy information (constancy_snd.v) and
by the checker (constancy.v). *)

(* A finite, efficient map from variables to values, used to represent
constancy information. [VarID.VarID_as_OT] is the same (modern,
[Orders]-style) ordered type already used for [VarSet] in liveness.v;
[FMapAVL] expects the legacy [OrderedType.OrderedType] interface, so
we bridge the two with [Backport_OT]. Defined once, outside the
[Constancy_info] functor, since it does not depend on the dialect. *)
Module VarID_legacy_OT := OrdersAlt.Backport_OT VarID.VarID_as_OT.
Module VarMap := FMapAVL.Make(VarID_legacy_OT).


Module Constancy_info (D: DIALECT).

  (* The one instance of [SmallStep(D)] (and hence of [CFGProg(D)]
  etc.) that the specification and the checker share: Coq's module
  system does not consider two separate applications of the same
  functor to the same argument interchangeable, so every other
  constancy file projects its program modules out of this one. *)
  Module SmallStepD := SmallStep(D).
  Module StateD := SmallStepD.StateD.
  Module CallStackD := StateD.CallStackD.
  Module StackFrameD := CallStackD.StackFrameD.
  Module LocalsD := StackFrameD.LocalsD.
  Module CFGProgD := SmallStepD.CFGProgD.
  Module CFGFunD := CFGProgD.CFGFunD.
  Module BlockD := CFGProgD.BlockD.
  Module PhiInfoD := BlockD.PhiInfoD.
  Module InstrD := BlockD.InstrD.
  Module ExitInfoD := BlockD.ExitInfoD.
  Module SimpleExprD := ExitInfoD.SimpleExprD.

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

  (* The constancy information at a program point is a finite map from
  variables to values: [x -> v] in the map means that [x] is known to
  be constant [v] there; a variable absent from the map is simply not
  known to be constant (it may or may not be, in reality).

  As with liveness, information is assigned for each block, and for
  every program point inside the block (0 being the first program
  point). Since optimizations that rely on this information query it
  at arbitrary program points -- not just at block boundaries -- we
  keep one map per program point rather than just a block-level
  summary. *)

  Definition pp_const_info_t := VarMap.t D.value_t.
  (* [block_const_info_t] has exactly one more entry than the block
  has instructions: entry [pc] is the info that holds right before
  instruction [pc]; the extra, trailing entry is the block-exit info
  (used when checking how blocks compose into a function). *)
  Definition block_const_info_t := list pp_const_info_t.
  Definition func_const_info_t := BlockID.t ->  option block_const_info_t.
  Definition prog_const_info_t := FuncName.t -> option func_const_info_t.

End Constancy_info.
