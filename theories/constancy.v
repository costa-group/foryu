Require Import FORYU.state.
Require Import FORYU.program.
Require Import FORYU.semantics.
Require Import FORYU.list_functions.
Require Import FORYU.constancy_snd.

From Stdlib Require Import Orders.
From Stdlib Require Import OrdersEx.
From Stdlib Require Import OrdersAlt.
From Stdlib Require Import FSets.FMapAVL.
From Stdlib Require Import MSets.
From Stdlib Require Import Arith.
From Stdlib Require Import List.
Import ListNotations.

From Stdlib  Require Import Relations.Relation_Operators.
Require Import stdpp.prelude.
Require Import stdpp.relations. (* This is where nsteps lives *)
From Stdlib Require Import Strings.Ascii.
Global Open Scope string_scope.

From Stdlib Require Import MSets.MSetAVL.
From Stdlib Require Import Structures.OrdersEx.      (* Provides New Keys *)

(* A finite, efficient map from variables to values, used to represent
constancy information. [VarID.VarID_as_OT] is the same (modern,
[Orders]-style) ordered type already used for [VarSet] in liveness.v;
[FMapAVL] expects the legacy [OrderedType.OrderedType] interface, so
we bridge the two with [Backport_OT]. Defined once, outside the
[Constancy] functor, since it does not depend on the dialect. *)
Module VarID_legacy_OT := OrdersAlt.Backport_OT VarID.VarID_as_OT.
Module VarMap := FMapAVL.Make(VarID_legacy_OT).


Module Constancy (D: DIALECT).

  (* Routed through [Constancy_snd(D)] (rather than calling
  [SmallStep(D)] independently, as this module used to) so that a
  downstream file connecting this checker to [Constancy_snd]'s
  relational spec sees the *same* [CFGProgD]/etc. -- Coq's module
  system does not consider two separate applications of the same
  functor to the same argument interchangeable, so two independent
  instantiations of [SmallStep(D)] would leave [check_const_program]'s
  own [CFGProgD.t] and [Constancy_snd(D).const_at_pc]'s unable to
  unify. *)
  Module ConstSndD := Constancy_snd(D).
  Module SmallStepD := ConstSndD.SmallStepD.
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

  (* Resolves a simple expression under the constancy info [pp]: a
  variable is resolved by looking it up in [pp], a value resolves to
  itself. *)
  Definition eval_sexpr_pp (pp: pp_const_info_t) (e: SimpleExprD.t) : option D.value_t :=
    match e with
    | inl v => VarMap.find v pp
    | inr val => Some val
    end.

  (* [m1] is checked to be a subset of [m2], i.e., every fact stated by
  [m1] is also stated (with the same value) by [m2]. This is the
  soundness criterion for one program point: whatever the analysis
  claims must be entailed by what is actually derivable; the analysis
  is free to be less precise (state fewer facts) than what could be
  derived, but never allowed to state a wrong fact. *)
  Definition const_info_subset (m1 m2: pp_const_info_t) : bool :=
    List.forallb
      (fun kv => match VarMap.find (fst kv) m2 with
                 | Some v2 => D.eqb (snd kv) v2
                 | None => false
                 end)
      (VarMap.elements m1).

  (* Pairs each variable in [vs] with the corresponding derived value
  in [vals] (in the same order), dropping variables for which nothing
  was derived ([None]). Yields [[]] if the two lists have different
  lengths. *)
  Fixpoint derive_pairs (vs: list VarID.t) (vals: list (option D.value_t)) : list (VarID.t * D.value_t) :=
    match vs, vals with
    | [], [] => []
    | v::vs', Some val::vals' => (v,val) :: derive_pairs vs' vals'
    | _::vs', None::vals' => derive_pairs vs' vals'
    | _, _ => []
    end.

  (* Updates [m] by first forgetting anything it stated about [vs]
  (they are being overwritten), then recording [pairs] (newly derived
  facts about some, possibly not all, of [vs]). *)
  Definition update_const_info (m: pp_const_info_t) (vs: list VarID.t) (pairs: list (VarID.t * D.value_t)) : pp_const_info_t :=
    let m' := List.fold_left (fun acc v => VarMap.remove v acc) vs m in
    List.fold_left (fun acc p => VarMap.add (fst p) (snd p) acc) pairs m'.

  (* Symbolically executes [instr] starting from the constancy info
  [Cb], yielding the actual post-info. This is the "ground truth" that
  a claimed post-info is checked against (it may be a subset of it,
  but never claim more).

     - For an assignment [ys := xs], each output is independent from
       the others: it gets the value resolved for the corresponding
       input under [Cb] (if any), and any prior fact about an output
       is dropped, since it is being overwritten. Variables that are
       not outputs keep whatever [Cb] said about them.

     - For an opcode, folding is only attempted when it does not
       depend on the dialect state ([D.opcode_indep_state]) and when
       all of its inputs are constant (unlike assignment, an opcode's
       result genuinely depends on all of its arguments at once).
       When folding succeeds and yields [Status.Running], the outputs
       get the computed values; otherwise nothing is derived for them
       (and any prior fact about them is still dropped).

     - For a function call, nothing can be derived statically, so
       nothing is recorded for the outputs (and any prior fact about
       them is dropped). *)
  Definition sym_exec_instr (instr: InstrD.t) (Cb: pp_const_info_t) : pp_const_info_t :=
    match instr.(InstrD.op) with
    | inr ASSIGN =>
        let values := List.map (eval_sexpr_pp Cb) instr.(input) in
        update_const_info Cb instr.(output) (derive_pairs instr.(output) values)
    | inl (inr opcode) =>
        match ListFunctions.option_list (List.map (eval_sexpr_pp Cb) instr.(input)) with
        | Some concrete_inputs =>
            if D.opcode_indep_state opcode then
              let '(res_vals, _, status) := D.execute_opcode D.empty_dialect_state opcode concrete_inputs in
              match status with
              | Status.Running =>
                  update_const_info Cb instr.(output) (derive_pairs instr.(output) (List.map (fun v => Some v) res_vals))
              | _ => update_const_info Cb instr.(output) []
              end
            else update_const_info Cb instr.(output) []
        | None => update_const_info Cb instr.(output) []
        end
    | inl (inl fname) =>
        update_const_info Cb instr.(output) []
    end.

  (* Checks the constancy information across a single instruction:
  [Cb] is the claimed info right before [instr], [Ca] is the claimed
  info right after it. This holds iff [Ca] is a subset of what is
  actually derivable by symbolically executing [instr] from [Cb]. *)
  Definition check_const_instr (instr: InstrD.t) (Cb Ca: pp_const_info_t) : bool :=
    const_info_subset Ca (sym_exec_instr instr Cb).

  (* Checks the constancy information across every program point of a
  block's instructions. [b_info] must have exactly one more entry
  than [instrs]: the extra, trailing entry is the block-exit info,
  which is not checked here -- it is checked once the whole function
  is considered, together with the block's neighbours. *)
  Fixpoint check_const_pp (instrs: list InstrD.t) (b_info: block_const_info_t) : bool :=
    match instrs, b_info with
    | [], _::[] => true
    | i::instrs', Cb::((Ca::_) as b_info') =>
        if check_const_instr i Cb Ca then
          check_const_pp instrs' b_info'
        else
          false
    | _, _ => false
    end.

  Definition check_const_block (r: prog_const_info_t) (f: FuncName.t) (b: BlockD.t) : bool :=
    match (r f) with (* Retrive function info *)
    | None => false
    | Some f_info =>
      match f_info b.(BlockD.bid) with (* Retrive block info *)
      | None => false
      | Some b_info =>
          check_const_pp b.(instructions) b_info
      end
    end.

  (* The entry (resp. exit) info of a block is the first (resp. last)
  entry of its [block_const_info_t]; both exist as soon as [b_info] is
  non-empty, which [check_const_pp] guarantees ([b_info] always has at
  least the one trailing/exit entry). *)
  Definition block_entry_info (b_info: block_const_info_t) : option pp_const_info_t :=
    List.hd_error b_info.

  Definition block_exit_info (b_info: block_const_info_t) : option pp_const_info_t :=
    List.hd_error (List.rev b_info).

  (* Checks that the entry info of block [next_bid] is consistent with
  the exit info [pred_exit] of one of its predecessors, [pred_bid]:
  the predecessor's exit, forward-transformed through the successor's
  phi-function for [pred_bid] (renamed/overwritten [out_vars], every
  other variable passed through unchanged -- exactly the transfer
  function [handle_jump_aux] in semantics.v applies at runtime), must
  entail the successor's claimed entry info. *)
  Definition check_const_successor (p: CFGProgD.t) (f_info: func_const_info_t) (fname: FuncName.t) (pred_bid: BlockID.t) (pred_exit: pp_const_info_t) (next_bid: BlockID.t) : bool :=
    match CFGProgD.get_block p fname next_bid with
    | None => false
    | Some next_b =>
        match f_info next_bid with
        | None => false
        | Some next_b_info =>
            match block_entry_info next_b_info with
            | None => false
            | Some next_entry =>
                let out_vars := fst next_b.(phi_function) in
                match snd next_b.(phi_function) pred_bid with
                | in_phi_info in_sexprs =>
                    let values := List.map (eval_sexpr_pp pred_exit) in_sexprs in
                    let transformed := update_const_info pred_exit out_vars (derive_pairs out_vars values) in
                    const_info_subset next_entry transformed
                end
            end
        end
    end.

  (* Checks that block [b]'s exit info is consistent with the entry
  info of every block it can jump to. [Terminate]/[ReturnBlock] have
  no successor within the function, so there is nothing to check --
  their claimed exit info is simply never consulted by anything
  intra-procedurally (a called function's outputs are always treated
  as unknown by [check_const_instr]'s function-call case). *)
  Definition check_const_edges (p: CFGProgD.t) (f_info: func_const_info_t) (fname: FuncName.t) (b: BlockD.t) (b_info: block_const_info_t) : bool :=
    match block_exit_info b_info with
    | None => false
    | Some b_exit =>
        match b.(exit_info) with
        | ExitInfoD.Terminate => true
        | ExitInfoD.ReturnBlock _ => true
        | ExitInfoD.Jump next_bid =>
            check_const_successor p f_info fname b.(bid) b_exit next_bid
        | ExitInfoD.ConditionalJump _ next_bid_if_true next_bid_if_false =>
            andb (check_const_successor p f_info fname b.(bid) b_exit next_bid_if_true)
                 (check_const_successor p f_info fname b.(bid) b_exit next_bid_if_false)
        end
    end.

  (* The general edge check above is vacuously true for the function's
  own entry block, since it has no predecessor within the function
  (nothing to falsify a claim there). We rule this out explicitly: the
  entry block's entry info must be empty -- nothing is known to be
  constant when a function starts, since this analysis is
  intra-procedural. *)
  Definition check_const_entry (f: CFGFunD.t) (b: BlockD.t) (b_info: block_const_info_t) : bool :=
    if BlockID.eqb b.(bid) f.(entry_bid) then
      match block_entry_info b_info with
      | Some m => VarMap.is_empty m
      | None => false
      end
    else
      true.

  (* Checks the constancy information of every block in [bs] -- the
  instructions within it, how it composes with its successors, and,
  if it is the function's entry block, that nothing is assumed at
  function start. *)
  Fixpoint check_const_blocks (bs: list BlockD.t) (f: CFGFunD.t) (p: CFGProgD.t) (r: prog_const_info_t) : bool :=
    match bs with
    | [] => true
    | b::bs' =>
        match r f.(name) with
        | None => false
        | Some f_info =>
            match f_info b.(bid) with
            | None => false
            | Some b_info =>
                if andb (andb (check_const_pp b.(instructions) b_info)
                              (check_const_edges p f_info f.(name) b b_info))
                        (check_const_entry f b b_info)
                then check_const_blocks bs' f p r
                else false
            end
        end
    end.

  (* Checks the constancy information of every block of every function
  in [fs] *)
  Fixpoint check_const_functions (fs: list CFGFunD.t) (p: CFGProgD.t) (r: prog_const_info_t) : bool :=
    match fs with
    | [] => true
    | f::fs' =>
        if check_const_blocks f.(blocks) f p r
        then check_const_functions fs' p r
        else false
    end.

  (* Checks the constancy information of every block of every function
  of the program [p] *)
  Definition check_const_program (p: CFGProgD.t) (r: prog_const_info_t) : bool :=
    check_const_functions p.(functions) p r.

End Constancy.
