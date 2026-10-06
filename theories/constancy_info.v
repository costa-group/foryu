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


(* ** Abstract execution of opcodes **

[CONST_SYMB D] collects the knowledge about the opcodes of dialect [D]
that the constancy analysis uses, separately from the dialect itself
(which only defines the semantics). [abs_exec op es known] is the
abstract execution of opcode [op] on the inputs [es] (variables or
values), where [known] gives the variables that are known to be
constant: it returns the known value of each output, if any, or [None]
if nothing is known. For example, it can evaluate an opcode whose
inputs are all known and whose result does not depend on the dialect
state, but also handle cases such as [x - x] or [x * 0] where some
inputs are unknown. [abs_exec_snd] states that it is correct: in any
dialect state, and for any values of the variables ([rho]) that agree
with [known], executing the opcode succeeds and produces the predicted
values. *)
Module Type CONST_SYMB (D: DIALECT).

  Parameter abs_exec :
    D.opcode_t -> list (VarID.t + D.value_t) -> (VarID.t -> option D.value_t) ->
    option (list (option D.value_t)).

  Parameter abs_exec_snd :
    forall (op: D.opcode_t) (es: list (VarID.t + D.value_t)) (known: VarID.t -> option D.value_t)
           (res: list (option D.value_t)) (st: D.dialect_state_t) (rho: VarID.t -> D.value_t),
      abs_exec op es known = Some res ->
      (forall (v: VarID.t) (c: D.value_t), known v = Some c -> rho v = c) ->
      exists (out: list D.value_t) (st': D.dialect_state_t),
        D.execute_opcode st op (List.map (fun e => match e with inl v => rho v | inr c => c end) es)
        = (out, st', Status.Running) /\
        (forall (k: nat) (c: D.value_t), nth_error res k = Some (Some c) -> nth_error out k = Some c).

End CONST_SYMB.

(* The trivial abstract execution, which never derives anything: it
can be used with any dialect *)
Module No_abs_exec (D: DIALECT) <: CONST_SYMB D.

  Definition abs_exec (op: D.opcode_t) (es: list (VarID.t + D.value_t)) (known: VarID.t -> option D.value_t)
    : option (list (option D.value_t)) := None.

  Lemma abs_exec_snd :
    forall (op: D.opcode_t) (es: list (VarID.t + D.value_t)) (known: VarID.t -> option D.value_t)
           (res: list (option D.value_t)) (st: D.dialect_state_t) (rho: VarID.t -> D.value_t),
      abs_exec op es known = Some res ->
      (forall (v: VarID.t) (c: D.value_t), known v = Some c -> rho v = c) ->
      exists (out: list D.value_t) (st': D.dialect_state_t),
        D.execute_opcode st op (List.map (fun e => match e with inl v => rho v | inr c => c end) es)
        = (out, st', Status.Running) /\
        (forall (k: nat) (c: D.value_t), nth_error res k = Some (Some c) -> nth_error out k = Some c).
  Proof.
    intros op es known res st rho H. discriminate H.
  Qed.

End No_abs_exec.


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
