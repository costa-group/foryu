Require Import FORYU.state.
Require Import FORYU.program.
Require Import FORYU.semantics.

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.

Module Constancy_snd (D: DIALECT).

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

  (* [is_predecessor_of p fname pred_bid bid pred_b] states that
  [pred_b] (the block with id [pred_bid] in function [fname]) has an
  edge into [bid], i.e., it jumps or conditionally jumps to it. *)
  Definition is_predecessor_of (p: CFGProgD.t) (fname: FuncName.t) (pred_bid bid: BlockID.t) (pred_b: BlockD.t) : Prop :=
    CFGProgD.get_block p fname pred_bid = Some pred_b /\
      match pred_b.(exit_info) with
      | ExitInfoD.Jump next_bid => next_bid = bid
      | ExitInfoD.ConditionalJump _ next_bid_if_true next_bid_if_false =>
          next_bid_if_true = bid \/ next_bid_if_false = bid
      | _ => False
      end.

  (* [phi_source b pred_bid v] tells us how [v] relates to [b]'s
  phi-function for predecessor [pred_bid]: [Some e] if [v] is one of
  [b]'s phi-defined variables, with [e] the corresponding simple
  expression to evaluate at [pred_bid]'s exit; [None] if [v] is not
  touched by the phi-function, in which case its value simply carries
  over unchanged from the predecessor. *)
  Definition phi_source (b: BlockD.t) (pred_bid: BlockID.t) (v: VarID.t) : option SimpleExprD.t :=
    let out_vars := fst b.(phi_function) in
    let in_sexprs := match snd b.(phi_function) pred_bid with in_phi_info es => es end in
    match List.find (fun ov => VarID.eqb (fst ov) v) (List.combine out_vars in_sexprs) with
    | Some (_, e) => Some e
    | None => None
    end.

  (* [const_out]/[const_in]/[const_at_pc]/[const_sexprs] characterize,
  mutually and coinductively, the exact/canonical set of "variable [v]
  is constant [c]" facts that hold at the exit/entry/an arbitrary
  program point of every block -- the most precise information a
  perfectly precise analysis could derive. [CoInductive] is needed for
  [const_out]/[const_in] because the CFG may contain loops, creating a
  cyclic dependency between a block's entry and the exit of a block
  that loops back into it (there is no acyclic order to bottom a plain
  [Inductive] derivation out on, exactly as for [live_out]/[live_in]
  in liveness_snd.v). Since [const_at_pc]/[const_sexprs] are defined
  together with them, Coq requires them to share the same
  [CoInductive] flavour -- even though their own recursion is
  perfectly well-founded on its own.

  Note that every occurrence of [const_out]/[const_in]/[const_at_pc]
  in the constructors below is either a direct hypothesis or sits
  inside a plain, inlined [match] -- never passed as a value to a
  separate helper function (e.g. an abstracted "does this simple
  expression resolve" helper parameterized over an arbitrary relation
  [R]). Coq's strict positivity checker only looks at containers it
  can see through (a bare hypothesis, an inline [match], another
  inductive type's own constructors); it does not unfold an arbitrary
  [Definition] to check whether *it* uses its argument positively, so
  routing through such a helper is rejected even though it would be
  semantically fine.

  A checker-validated (and hence possibly less precise) result's
  claims will later be shown to be implied by this ground truth --
  that is the semantic content we are ultimately after. *)
  CoInductive const_out (p: CFGProgD.t) : FuncName.t -> BlockID.t -> VarID.t -> D.value_t -> Prop :=
  | const_out_any (fname: FuncName.t) (bid: BlockID.t) (b: BlockD.t) (v: VarID.t) (c: D.value_t) :
    CFGProgD.get_block p fname bid = Some b ->
    const_at_pc p fname bid (length b.(instructions)) v c ->
    const_out p fname bid v c

  with const_in (p: CFGProgD.t) : FuncName.t -> BlockID.t -> VarID.t -> D.value_t -> Prop :=
  | const_in_merge (fname: FuncName.t) (f: CFGFunD.t) (bid: BlockID.t) (b: BlockD.t) (v: VarID.t) (c: D.value_t) :
    CFGProgD.get_func p fname = Some f ->
    bid <> f.(entry_bid) -> (* nothing is constant at a function's own
    entry, since we do not track anything across calls; leaving the
    entry block out of this constructor -- and giving it no
    constructor of its own -- means nothing is ever derivable there,
    exactly as intended *)
    CFGProgD.get_block p fname bid = Some b ->
    (* Unlike [InstrD.t]'s own [output], [BlockD.t]'s phi-function
    out-vars carry no built-in [NoDup] invariant, yet [phi_source]
    (first-match, via [List.find]) and the actual runtime effect of a
    jump (last-write-wins, via [LocalsD.set_all] processing pairs
    left-to-right) only agree when there are no duplicates -- so
    soundness genuinely depends on this holding, exactly as
    [InstrD.H_nodup] does for plain assignments/opcodes. *)
    NoDup (fst b.(phi_function)) ->
    (* [c] must be entailed by *every* predecessor -- unlike
    liveness's successors (always exactly the two branches of a
    conditional jump, known from a block's own exit_info), a block's
    predecessors are not bounded by anything local to its own
    definition, so we quantify over them explicitly. *)
    (* Written as an explicit disjunction/conjunction rather than a
    [match] on [phi_source b pred_bid v]: Coq's strict positivity
    checker does not look through a [match] whose branches mix
    [const_out ...] with unrelated terms, so we spell the same case
    split out using plain logical connectives instead, which it does
    understand as positive. *)
    (forall pred_bid pred_b,
        is_predecessor_of p fname pred_bid bid pred_b ->
        (phi_source b pred_bid v = None /\ const_out p fname pred_bid v c)
        \/ (exists v', phi_source b pred_bid v = Some (inl v') /\ const_out p fname pred_bid v' c)
        \/ (exists val, phi_source b pred_bid v = Some (inr val) /\ c = val)) ->
    const_in p fname bid v c

  with const_at_pc (p: CFGProgD.t) : FuncName.t -> BlockID.t -> nat -> VarID.t -> D.value_t -> Prop :=
  | const_at_pc_entry (fname: FuncName.t) (bid: BlockID.t) (v: VarID.t) (c: D.value_t) :
    const_in p fname bid v c ->
    const_at_pc p fname bid 0 v c

  (* An instruction that does not write [v] leaves it unaffected,
  regardless of its kind (assignment, opcode, or function call: all of
  them only ever change the locals named in their own [output]). *)
  | const_at_pc_unaffected (fname: FuncName.t) (bid: BlockID.t) (pc: nat) (b: BlockD.t) (i: InstrD.t) (v: VarID.t) (c: D.value_t) :
    CFGProgD.get_block p fname bid = Some b ->
    nth_error b.(instructions) pc = Some i ->
    ~ In v i.(output) ->
    const_at_pc p fname bid pc v c ->
    const_at_pc p fname bid (S pc) v c

  (* [ys := xs]: each output is independent of the others, and gets
  whatever value its corresponding input resolves to. *)
  | const_at_pc_assign (fname: FuncName.t) (bid: BlockID.t) (pc: nat) (b: BlockD.t) (i: InstrD.t) (v: VarID.t) (c: D.value_t) (k: nat) (x: SimpleExprD.t) :
    CFGProgD.get_block p fname bid = Some b ->
    nth_error b.(instructions) pc = Some i ->
    i.(InstrD.op) = inr ASSIGN ->
    nth_error i.(output) k = Some v ->
    nth_error i.(input) k = Some x ->
    ((exists v', x = inl v' /\ const_at_pc p fname bid pc v' c)
     \/ (exists val, x = inr val /\ c = val)) ->
    const_at_pc p fname bid (S pc) v c

  (* An opcode's output is constant only when the opcode does not
  depend on the dialect state and all of its inputs are constant at
  once (unlike assignment, an opcode's result genuinely depends on all
  of its arguments together), and folding it actually keeps running. *)
  | const_at_pc_opcode (fname: FuncName.t) (bid: BlockID.t) (pc: nat) (b: BlockD.t) (i: InstrD.t) (opcode: D.opcode_t) (v: VarID.t) (c: D.value_t) (k: nat) (concrete_inputs res_vals: list D.value_t) (st: D.dialect_state_t) :
    CFGProgD.get_block p fname bid = Some b ->
    nth_error b.(instructions) pc = Some i ->
    i.(InstrD.op) = inl (inr opcode) ->
    D.opcode_indep_state opcode = true ->
    const_sexprs p fname bid pc i.(input) concrete_inputs ->
    D.execute_opcode D.empty_dialect_state opcode concrete_inputs = (res_vals, st, Status.Running) ->
    nth_error i.(output) k = Some v ->
    nth_error res_vals k = Some c ->
    const_at_pc p fname bid (S pc) v c

  (* A function call's outputs are never constant: there is simply no
  constructor deriving [const_at_pc] for them, which is exactly what
  we want -- nothing is known statically about a callee's results. *)

  (* [const_sexprs p fname bid pc es cs] states that every simple
  expression in [es] resolves (under the constancy info at program
  point [pc]) to the corresponding value in [cs] -- the pointwise,
  all-inputs-at-once counterpart of a single [const_at_pc]/literal
  check, needed because [const_at_pc_opcode] requires *every* input to
  be constant simultaneously to fold an opcode. This plays the same
  role [ListFunctions.option_list]/[Forall2] would, but is defined as
  part of this same mutual family so that its use of [const_at_pc]
  stays a direct constructor argument (seenote above on strict
  positivity). *)
  with const_sexprs (p: CFGProgD.t) : FuncName.t -> BlockID.t -> nat -> list SimpleExprD.t -> list D.value_t -> Prop :=
  | const_sexprs_nil (fname: FuncName.t) (bid: BlockID.t) (pc: nat) :
    const_sexprs p fname bid pc [] []
  | const_sexprs_cons_var (fname: FuncName.t) (bid: BlockID.t) (pc: nat) (v: VarID.t) (c: D.value_t) (es: list SimpleExprD.t) (cs: list D.value_t) :
    const_at_pc p fname bid pc v c ->
    const_sexprs p fname bid pc es cs ->
    const_sexprs p fname bid pc (inl v :: es) (c :: cs)
  | const_sexprs_cons_val (fname: FuncName.t) (bid: BlockID.t) (pc: nat) (val: D.value_t) (es: list SimpleExprD.t) (cs: list D.value_t) :
    const_sexprs p fname bid pc es cs ->
    const_sexprs p fname bid pc (inr val :: es) (val :: cs).

  (* Re-exposes [const_out]'s single constructor as a plain existential.
  Destructuring [const_out p fname bid v c] directly, at a call site
  where [bid] (or [fname]/[v]/[c]) is some compound term rather than a
  bare local variable (e.g. [curr_bid sf_mid]), drags Coq's dependent
  case-analysis machinery into generalizing that term across the whole
  context -- including hypotheses that merely happen to mention the
  same subterm elsewhere (e.g. anything else about [sf_mid]) -- which
  can silently destruct far more than intended. Routing through a
  once-and-for-all [exists] here keeps every call site a completely
  ordinary (non-dependent) destructuring. *)
  Lemma const_out_inv :
    forall (p: CFGProgD.t) (fname: FuncName.t) (bid: BlockID.t) (v: VarID.t) (c: D.value_t),
      const_out p fname bid v c ->
      exists b, CFGProgD.get_block p fname bid = Some b /\ const_at_pc p fname bid (length b.(instructions)) v c.
  Proof.
    intros p fname bid v c H.
    destruct H as [fname' bid' b' v' c' Hb Hat].
    exists b'. split; assumption.
  Qed.

  (* [SmallStepD.eval] recurses on its *first* step ([eval (S n) s p =
  eval n (step s p) p]). To reason about the *last* step taken to
  reach a state -- matching how [const_at_pc]'s own constructors are
  most naturally unfolded (from a fact at [S pc]/[bid], back to one at
  [pc]/a predecessor) -- we need the reverse decomposition: [S n]
  steps is [n] steps followed by one more [step]. *)
  Lemma eval_split_last :
    forall (n: nat) (p: CFGProgD.t) (s sn: StateD.t),
      SmallStepD.eval (S n) s p = Some sn ->
      exists s_mid, SmallStepD.eval n s p = Some s_mid /\ SmallStepD.step s_mid p = Some sn.
  Proof.
    induction n as [| n' IHn'].
    - intros p s sn H.
      simpl in H.
      destruct (SmallStepD.step s p) as [s1|] eqn:E_step; try discriminate.
      injection H as H.
      subst s1.
      exists s.
      split.
      + reflexivity.
      + exact E_step.
    - intros p s sn H.
      simpl in H.
      destruct (SmallStepD.step s p) as [s1|] eqn:E_step; try discriminate.
      destruct (IHn' p s1 sn H) as [s_mid [H_eval H_step]].
      exists s_mid.
      split.
      + simpl. rewrite E_step. exact H_eval.
      + exact H_step.
  Qed.

  (* [step] only ever inspects/rewrites the *head* of the call stack:
  it either replaces the head in place (a plain instruction, a jump, a
  cond-jump, or an error -- all keep [rsf] as-is), pushes a fresh frame
  on top of it (a function call: [rsf] is still there, one level
  deeper), or -- if [rsf] itself is non-empty -- pops the head away and
  updates [rsf]'s own head (a return). Either way, anything two levels
  down or more is completely untouched by a single step; this is the
  fact that lets us "skip over" an entire nested call later as a black
  box. *)
  Lemma step_call_stack_shape :
    forall (p: CFGProgD.t) (s s': StateD.t) (sf: StackFrameD.t) (rsf: CallStackD.t),
      s.(StateD.call_stack) = sf :: rsf ->
      SmallStepD.step s p = Some s' ->
      (exists sf', s'.(StateD.call_stack) = sf' :: rsf)
      \/ (exists sf' b instr callee,
            CFGProgD.get_block p (StackFrameD.fname sf) (StackFrameD.curr_bid sf) = Some b /\
            nth_error (BlockD.instructions b) (StackFrameD.pc sf) = Some instr /\
            InstrD.op instr = inl (inl callee) /\
            s'.(StateD.call_stack) = sf' :: sf :: rsf)
      \/ (exists sf' rsf' sf'', rsf = sf' :: rsf' /\ s'.(StateD.call_stack) = sf'' :: rsf').
  Proof.
    intros p s s' sf rsf Hs Hstep.
    unfold SmallStepD.step in Hstep.
    destruct (StateD.status s) eqn:Hstatus; try discriminate.
    unfold SmallStepD.get_next_instr in Hstep.
    rewrite Hs in Hstep.
    destruct (CFGProgD.get_instr p (StackFrameD.fname sf) (StackFrameD.curr_bid sf) (StackFrameD.pc sf)) as [instr|] eqn:Hinstr.
    - (* execute_instr: assign / opcode / function call *)
      injection Hstep as Hstep; subst s'.
      unfold SmallStepD.execute_instr.
      rewrite Hs.
      destruct (InstrD.op instr) as [[callee|opcode]|aux] eqn:Hop.
      + (* function call: push on success, otherwise an error (same rsf) *)
        assert (Hcall_instr : exists b, CFGProgD.get_block p (StackFrameD.fname sf) (StackFrameD.curr_bid sf) = Some b
                                         /\ nth_error (BlockD.instructions b) (StackFrameD.pc sf) = Some instr).
        { unfold CFGProgD.get_instr in Hinstr.
          destruct (CFGProgD.get_block p (StackFrameD.fname sf) (StackFrameD.curr_bid sf)) as [b|] eqn:Hb; try discriminate.
          exists b. split; [reflexivity | exact Hinstr]. }
        destruct Hcall_instr as [b [Hb Hnthb]].
        unfold SmallStepD.execute_func.
        destruct (CFGProgD.get_func p callee) as [func|] eqn:Hfunc.
        * destruct (LocalsD.set_all LocalsD.empty (CFGFunD.args func) (SmallStepD.eval_sexpr (InstrD.input instr) sf)) as [locals'|] eqn:Hset.
          -- right; left. eexists. exists b, instr, callee.
             split; [exact Hb | split; [exact Hnthb | split; [exact Hop | simpl; reflexivity]]].
          -- left. eexists. unfold SmallStepD.error. simpl. rewrite Hs. reflexivity.
        * left. eexists. unfold SmallStepD.error. simpl. rewrite Hs. reflexivity.
      + (* opcode: same rsf, top replaced *)
        left.
        unfold SmallStepD.execute_opcode.
        destruct (D.execute_opcode (StateD.dialect_state s) opcode (SmallStepD.eval_sexpr (InstrD.input instr) sf)) as [[out_vals dialect_state'] status'].
        unfold SmallStepD.execute_assignment.
        destruct (LocalsD.set_all (StackFrameD.locals sf) (InstrD.output instr) out_vals) as [locals'|] eqn:Hset.
        * eexists. simpl. reflexivity.
        * eexists. unfold SmallStepD.error. simpl. rewrite Hs. reflexivity.
      + (* assign: same rsf, top replaced *)
        destruct aux.
        left.
        unfold SmallStepD.execute_assignment.
        destruct (LocalsD.set_all (StackFrameD.locals sf) (InstrD.output instr) (SmallStepD.eval_sexpr (InstrD.input instr) sf)) as [locals'|] eqn:Hset.
        * eexists. simpl. reflexivity.
        * eexists. unfold SmallStepD.error. simpl. rewrite Hs. reflexivity.
    - (* handle_block_exit: jump / cond-jump / return / terminate *)
      injection Hstep as Hstep; subst s'.
      unfold SmallStepD.handle_block_exit.
      rewrite Hs.
      destruct (CFGProgD.get_block p (StackFrameD.fname sf) (StackFrameD.curr_bid sf)) as [b|] eqn:Hblock.
      + destruct (BlockD.exit_info b) as [cond_var_id bid_if_true bid_if_false | jbid | ret_sexprs | ] eqn:Hexit.
        * (* ConditionalJump: same rsf *)
          left.
          unfold SmallStepD.handle_cond_jump.
          destruct (D.is_true_value (LocalsD.get (StackFrameD.locals sf) cond_var_id));
            unfold SmallStepD.handle_jump;
            [ destruct (CFGProgD.get_block p (StackFrameD.fname sf) bid_if_true) as [next_b|] eqn:Hnb
            | destruct (CFGProgD.get_block p (StackFrameD.fname sf) bid_if_false) as [next_b|] eqn:Hnb ];
            try (eexists; unfold SmallStepD.error; simpl; rewrite Hs; reflexivity);
            destruct (snd (BlockD.phi_function next_b) (StackFrameD.curr_bid sf)) eqn:Hphi;
            unfold SmallStepD.handle_jump_aux;
            destruct (LocalsD.set_all (StackFrameD.locals sf) (fst (BlockD.phi_function next_b)) (SmallStepD.eval_sexpr in_sexprs sf)) as [locals'|] eqn:Hset;
            (eexists; simpl; reflexivity) || (eexists; unfold SmallStepD.error; simpl; rewrite Hs; reflexivity).
        * (* Jump: same rsf *)
          left.
          unfold SmallStepD.handle_jump.
          destruct (CFGProgD.get_block p (StackFrameD.fname sf) jbid) as [next_b|] eqn:Hnb.
          -- destruct (snd (BlockD.phi_function next_b) (StackFrameD.curr_bid sf)) eqn:Hphi.
             unfold SmallStepD.handle_jump_aux.
             destruct (LocalsD.set_all (StackFrameD.locals sf) (fst (BlockD.phi_function next_b)) (SmallStepD.eval_sexpr in_sexprs sf)) as [locals'|] eqn:Hset.
             ++ eexists. simpl. reflexivity.
             ++ eexists. unfold SmallStepD.error. simpl. rewrite Hs. reflexivity.
          -- eexists. unfold SmallStepD.error. simpl. rewrite Hs. reflexivity.
        * (* ReturnBlock: pops [sf] and updates the frame below it on
          success (case 3); any failure along the way leaves the
          *entire original* stack untouched, [sf] included (case 1) --
          every failing branch below calls [error] on our own, outer
          [s], not on any partially-updated state. *)
          unfold SmallStepD.handle_return.
          destruct rsf as [| sf' rsf'] eqn:Hrsf.
          -- left. eexists. unfold SmallStepD.error. simpl. rewrite Hs. reflexivity.
          -- destruct (CFGProgD.get_block p (StackFrameD.fname sf') (StackFrameD.curr_bid sf')) as [b'|] eqn:Hblock'.
             ++ destruct (List.nth_error (BlockD.instructions b') (StackFrameD.pc sf')) as [instr'|] eqn:Hnth'.
                ** unfold SmallStepD.execute_assignment.
                   destruct (LocalsD.set_all (StackFrameD.locals sf') (InstrD.output instr') (SmallStepD.eval_sexpr ret_sexprs sf)) as [locals'|] eqn:Hset.
                   --- right; right.
                       exists sf', rsf', {| fname := StackFrameD.fname sf'; locals := locals'; curr_bid := StackFrameD.curr_bid sf'; pc := StackFrameD.pc sf' + 1 |}.
                       split; [reflexivity | simpl; reflexivity].
                   --- left. eexists. unfold SmallStepD.error. simpl. rewrite Hs. reflexivity.
                ** left. eexists. unfold SmallStepD.error. simpl. rewrite Hs. reflexivity.
             ++ left. eexists. unfold SmallStepD.error. simpl. rewrite Hs. reflexivity.
        * (* Terminate: same rsf, top unchanged (only status changes) *)
          left.
          unfold SmallStepD.handle_terminate.
          eexists. simpl. rewrite Hs. reflexivity.
      + (* block not found: error, same rsf *)
        left. eexists. unfold SmallStepD.error. simpl. rewrite Hs. reflexivity.
  Qed.

  (* The converse direction we actually need for the induction: if,
  *after* one step, our target frame [fr] is buried under a non-empty
  prefix [a :: hl'] (on top of [rest]), then it must *already* have
  been sitting on [rest] (under some, possibly different, prefix)
  *before* that step -- a single step can only ever touch what's at
  or very near the top, never reach all the way down to [fr]/[rest]
  and disturb them, whichever of [step_call_stack_shape]'s three cases
  it turns out to be. *)
  Lemma step_preserves_buried_frame :
    forall (p: CFGProgD.t) (s s': StateD.t) (a: StackFrameD.t) (hl' rest: CallStackD.t) (fr: StackFrameD.t),
      s'.(StateD.call_stack) = (a :: hl') ++ fr :: rest ->
      SmallStepD.step s p = Some s' ->
      exists hl'', s.(StateD.call_stack) = hl'' ++ fr :: rest.
  Proof.
    intros p s s' a hl' rest fr Hs' Hstep.
    destruct (s.(StateD.call_stack)) as [| sf rsf] eqn:Hscs.
    - exfalso.
      unfold SmallStepD.step in Hstep.
      destruct (StateD.status s); try discriminate.
      unfold SmallStepD.get_next_instr in Hstep.
      rewrite Hscs in Hstep.
      injection Hstep as Hstep.
      subst s'.
      unfold SmallStepD.handle_block_exit in Hs'.
      rewrite Hscs in Hs'.
      unfold SmallStepD.error in Hs'.
      simpl in Hs'.
      rewrite Hscs in Hs'.
      discriminate Hs'.
    - destruct (step_call_stack_shape p s s' sf rsf Hscs Hstep)
        as [[sf' Hcase1] | [[sf' [b2 [instr2 [callee2 [Hb2 [Hnth2 [Hop2 Hcase2]]]]]]] | [sf2 [rsf2 [sf'' [Hrsf Hcase3]]]]]].
      + rewrite Hcase1 in Hs'.
        injection Hs' as Ha Hrsf_eq.
        exists (sf :: hl').
        simpl. rewrite Hrsf_eq. reflexivity.
      + rewrite Hcase2 in Hs'.
        injection Hs' as Ha Heq.
        exists hl'.
        exact Heq.
      + rewrite Hcase3 in Hs'.
        injection Hs' as Ha Heq.
        exists (sf :: sf2 :: hl').
        simpl. rewrite Hrsf. simpl. rewrite Heq. reflexivity.
  Qed.

  (* [frame_pc_is_call p fr] states that [fr] is currently sitting at
  a function-call instruction -- the fact that must hold of any frame
  found directly below another one in a *reachable* call stack (it is
  the frame that made the call the frame above it is a callee of).
  Nothing in [step]/[handle_return] checks this on its own --
  [handle_return] happily assigns return values into whatever
  instruction happens to sit at the target program point, regardless
  of its kind -- so this has to be tracked as a genuine invariant of
  reachable executions, not derived from any single step. *)
  Definition frame_pc_is_call (p: CFGProgD.t) (fr: StackFrameD.t) : Prop :=
    exists b instr callee,
      CFGProgD.get_block p (StackFrameD.fname fr) (StackFrameD.curr_bid fr) = Some b /\
      nth_error (BlockD.instructions b) (StackFrameD.pc fr) = Some instr /\
      InstrD.op instr = inl (inl callee).

  (* A call stack is well-formed when every frame that has another
  frame directly above it (i.e., every frame except the very last,
  bottom-most one) satisfies [frame_pc_is_call]. *)
  Fixpoint call_stack_wf (p: CFGProgD.t) (cs: CallStackD.t) : Prop :=
    match cs with
    | [] => True
    | _ :: [] => True
    | _ :: ((next :: _) as tail) => frame_pc_is_call p next /\ call_stack_wf p tail
    end.

  Lemma step_preserves_call_stack_wf :
    forall (p: CFGProgD.t) (s s': StateD.t),
      call_stack_wf p s.(StateD.call_stack) ->
      SmallStepD.step s p = Some s' ->
      call_stack_wf p s'.(StateD.call_stack).
  Proof.
    intros p s s' Hwf Hstep.
    destruct (s.(StateD.call_stack)) as [| sf rsf] eqn:Hscs.
    - unfold SmallStepD.step in Hstep.
      destruct (StateD.status s); try discriminate.
      unfold SmallStepD.get_next_instr in Hstep.
      rewrite Hscs in Hstep.
      injection Hstep as Hstep.
      subst s'.
      unfold SmallStepD.handle_block_exit.
      rewrite Hscs.
      unfold SmallStepD.error.
      simpl.
      rewrite Hscs.
      exact I.
    - destruct (step_call_stack_shape p s s' sf rsf Hscs Hstep)
        as [[sf' Hcase1] | [[sf' [b2 [instr2 [callee2 [Hb2 [Hnth2 [Hop2 Hcase2]]]]]]] | [sf2 [rsf2 [sf'' [Hrsf Hcase3]]]]]].
      + rewrite Hcase1.
        destruct rsf as [| r1 rtail].
        * simpl. exact I.
        * simpl in Hwf. simpl. exact Hwf.
      + rewrite Hcase2.
        simpl.
        split.
        * exists b2, instr2, callee2. repeat split; assumption.
        * exact Hwf.
      + rewrite Hcase3.
        rewrite Hrsf in Hwf.
        simpl in Hwf.
        destruct Hwf as [Hfcall Hwfrest].
        destruct rsf2 as [| r2 rtail2].
        * simpl. exact I.
        * simpl in Hwfrest. simpl. exact Hwfrest.
  Qed.

  Lemma eval_preserves_call_stack_wf :
    forall (n: nat) (p: CFGProgD.t) (s0 sn: StateD.t),
      call_stack_wf p s0.(StateD.call_stack) ->
      SmallStepD.eval n s0 p = Some sn ->
      call_stack_wf p sn.(StateD.call_stack).
  Proof.
    induction n as [| n' IHn'].
    - intros p s0 sn Hwf Heval.
      simpl in Heval.
      injection Heval as Heval.
      subst sn.
      exact Hwf.
    - intros p s0 sn Hwf Heval.
      simpl in Heval.
      destruct (SmallStepD.step s0 p) as [s1|] eqn:Hstep; try discriminate.
      exact (IHn' p s1 sn (step_preserves_call_stack_wf p s0 s1 Hwf Hstep) Heval).
  Qed.

  (* [const_out]/[const_at_pc_entry] characterize a block's exit point
  as exactly [length b.(instructions)] -- but [step] only ever learns
  that a frame's [pc] has run *off the end* of its block
  ([get_next_instr]/[get_instr] returning [None], i.e. [pc >=
  length(...)]), not that it sits *exactly* at that boundary. The two
  coincide only because [pc] can never overshoot it in the first place:
  every place [step] advances a frame's own [pc] (an ordinary
  instruction, or the assignment [handle_return] performs into the
  frame below) does so from a position where [get_instr]/[nth_error]
  had just *succeeded* -- which itself proves the pre-advance [pc] was
  *strictly* below the length, hence the post-advance one is at most
  it. Every place [step] resets a frame's [pc] to [0] (jump, cond-jump,
  a freshly pushed call) trivially satisfies the bound too. So, unlike
  [call_stack_wf], this invariant needs no assumption about the frame
  below the top -- it is reestablished fresh at every single step. *)
  Definition top_pc_wf (p: CFGProgD.t) (cs: CallStackD.t) : Prop :=
    match cs with
    | [] => True
    | sf :: _ =>
        forall b, CFGProgD.get_block p (StackFrameD.fname sf) (StackFrameD.curr_bid sf) = Some b ->
                  StackFrameD.pc sf <= length b.(instructions)
    end.

  Lemma step_preserves_top_pc_wf :
    forall (p: CFGProgD.t) (s s': StateD.t),
      top_pc_wf p s.(StateD.call_stack) ->
      SmallStepD.step s p = Some s' ->
      top_pc_wf p s'.(StateD.call_stack).
  Proof.
    intros p s s' Hwf Hstep.
    unfold SmallStepD.step in Hstep.
    destruct (s.(StateD.call_stack)) as [| sf rsf] eqn:Hscs.
    - destruct (StateD.status s); try discriminate.
      unfold SmallStepD.get_next_instr in Hstep.
      rewrite Hscs in Hstep.
      injection Hstep as Hstep.
      subst s'.
      unfold SmallStepD.handle_block_exit.
      rewrite Hscs.
      unfold SmallStepD.error.
      simpl.
      rewrite Hscs.
      exact I.
    - destruct (StateD.status s); try discriminate.
      unfold SmallStepD.get_next_instr in Hstep.
      rewrite Hscs in Hstep.
      destruct (CFGProgD.get_instr p (StackFrameD.fname sf) (StackFrameD.curr_bid sf) (StackFrameD.pc sf)) as [instr|] eqn:Hinstr.
      + (* execute_instr fired *)
        injection Hstep as Hstep.
        subst s'.
        unfold SmallStepD.execute_instr.
        rewrite Hscs.
        destruct (InstrD.op instr) as [[callee|opcode]|aux] eqn:Hop.
        * (* function call *)
          unfold SmallStepD.execute_func.
          destruct (CFGProgD.get_func p callee) as [func|] eqn:Hfunc.
          -- destruct (LocalsD.set_all LocalsD.empty (CFGFunD.args func) (SmallStepD.eval_sexpr (InstrD.input instr) sf)) as [locals'|] eqn:Hset.
             ++ (* push: fresh frame, pc = 0 *)
                simpl. intros b' Hb'. lia.
             ++ (* error: unchanged *)
                unfold SmallStepD.error. simpl. rewrite Hscs. exact Hwf.
          -- unfold SmallStepD.error. simpl. rewrite Hscs. exact Hwf.
        * (* opcode *)
          unfold SmallStepD.execute_opcode.
          destruct (D.execute_opcode (StateD.dialect_state s) opcode (SmallStepD.eval_sexpr (InstrD.input instr) sf))
            as [[out_vals dialect_state'] status'].
          unfold SmallStepD.execute_assignment.
          destruct (LocalsD.set_all (StackFrameD.locals sf) (InstrD.output instr) out_vals) as [locals'|] eqn:Hset.
          -- simpl. intros b' Hb'.
             unfold CFGProgD.get_instr in Hinstr.
             rewrite Hb' in Hinstr.
             assert (Hbound : StackFrameD.pc sf < length (BlockD.instructions b')).
             { apply List.nth_error_Some. rewrite Hinstr. congruence. }
             lia.
          -- unfold SmallStepD.error. simpl. rewrite Hscs. exact Hwf.
        * (* assign *)
          destruct aux.
          unfold SmallStepD.execute_assignment.
          destruct (LocalsD.set_all (StackFrameD.locals sf) (InstrD.output instr) (SmallStepD.eval_sexpr (InstrD.input instr) sf)) as [locals'|] eqn:Hset.
          -- simpl. intros b' Hb'.
             unfold CFGProgD.get_instr in Hinstr.
             rewrite Hb' in Hinstr.
             assert (Hbound : StackFrameD.pc sf < length (BlockD.instructions b')).
             { apply List.nth_error_Some. rewrite Hinstr. congruence. }
             lia.
          -- unfold SmallStepD.error. simpl. rewrite Hscs. exact Hwf.
      + (* handle_block_exit fired *)
        injection Hstep as Hstep.
        subst s'.
        unfold SmallStepD.handle_block_exit.
        rewrite Hscs.
        destruct (CFGProgD.get_block p (StackFrameD.fname sf) (StackFrameD.curr_bid sf)) as [b|] eqn:Hblock.
        * destruct (BlockD.exit_info b) as [cond_var bt bf | jbid | rets | ] eqn:Hexit.
          -- (* ConditionalJump *)
             unfold SmallStepD.handle_cond_jump.
             simpl.
             destruct (D.is_true_value (LocalsD.get (StackFrameD.locals sf) cond_var)).
             ++ unfold SmallStepD.handle_jump.
                destruct (CFGProgD.get_block p (StackFrameD.fname sf) bt) as [nb|] eqn:Hnb.
                ** unfold SmallStepD.handle_jump_aux.
                   destruct (snd (BlockD.phi_function nb) (StackFrameD.curr_bid sf)) eqn:Hphi.
                   destruct (LocalsD.set_all (StackFrameD.locals sf) (fst (BlockD.phi_function nb)) (SmallStepD.eval_sexpr in_sexprs sf)) as [locals'|] eqn:Hset.
                   --- simpl. intros b' Hb'. lia.
                   --- unfold SmallStepD.error. simpl. rewrite Hscs. exact Hwf.
                ** unfold SmallStepD.error. simpl. rewrite Hscs. exact Hwf.
             ++ unfold SmallStepD.handle_jump.
                destruct (CFGProgD.get_block p (StackFrameD.fname sf) bf) as [nb|] eqn:Hnb.
                ** unfold SmallStepD.handle_jump_aux.
                   destruct (snd (BlockD.phi_function nb) (StackFrameD.curr_bid sf)) eqn:Hphi.
                   destruct (LocalsD.set_all (StackFrameD.locals sf) (fst (BlockD.phi_function nb)) (SmallStepD.eval_sexpr in_sexprs sf)) as [locals'|] eqn:Hset.
                   --- simpl. intros b' Hb'. lia.
                   --- unfold SmallStepD.error. simpl. rewrite Hscs. exact Hwf.
                ** unfold SmallStepD.error. simpl. rewrite Hscs. exact Hwf.
          -- (* Jump *)
             unfold SmallStepD.handle_jump.
             destruct (CFGProgD.get_block p (StackFrameD.fname sf) jbid) as [nb|] eqn:Hnb.
             ++ unfold SmallStepD.handle_jump_aux.
                destruct (snd (BlockD.phi_function nb) (StackFrameD.curr_bid sf)) eqn:Hphi.
                destruct (LocalsD.set_all (StackFrameD.locals sf) (fst (BlockD.phi_function nb)) (SmallStepD.eval_sexpr in_sexprs sf)) as [locals'|] eqn:Hset.
                ** simpl. intros b' Hb'. lia.
                ** unfold SmallStepD.error. simpl. rewrite Hscs. exact Hwf.
             ++ unfold SmallStepD.error. simpl. rewrite Hscs. exact Hwf.
          -- (* ReturnBlock *)
             unfold SmallStepD.handle_return.
             destruct rsf as [| sf2 rsf2] eqn:Hrsf.
             ++ unfold SmallStepD.error. simpl. rewrite Hscs. exact Hwf.
             ++ destruct (CFGProgD.get_block p (StackFrameD.fname sf2) (StackFrameD.curr_bid sf2)) as [b2|] eqn:Hb2.
                ** destruct (List.nth_error (BlockD.instructions b2) (StackFrameD.pc sf2)) as [instr2|] eqn:Hnth2.
                   --- unfold SmallStepD.execute_assignment.
                       destruct (LocalsD.set_all (StackFrameD.locals sf2) (InstrD.output instr2) (SmallStepD.eval_sexpr rets sf)) as [locals2'|] eqn:Hset2.
                       +++ simpl. intros b' Hb'.
                           rewrite Hb2 in Hb'. injection Hb' as Hb'. subst b'.
                           assert (Hbound : StackFrameD.pc sf2 < length (BlockD.instructions b2))
                             by (apply List.nth_error_Some; rewrite Hnth2; congruence).
                           lia.
                       +++ unfold SmallStepD.error. simpl. rewrite Hscs. exact Hwf.
                   --- unfold SmallStepD.error. simpl. rewrite Hscs. exact Hwf.
                ** unfold SmallStepD.error. simpl. rewrite Hscs. exact Hwf.
          -- (* Terminate *)
             unfold SmallStepD.handle_terminate.
             simpl. rewrite Hscs. exact Hwf.
        * unfold SmallStepD.error. simpl. rewrite Hscs. exact Hwf.
  Qed.

  Lemma eval_preserves_top_pc_wf :
    forall (n: nat) (p: CFGProgD.t) (s0 sn: StateD.t),
      top_pc_wf p s0.(StateD.call_stack) ->
      SmallStepD.eval n s0 p = Some sn ->
      top_pc_wf p sn.(StateD.call_stack).
  Proof.
    induction n as [| n' IHn'].
    - intros p s0 sn Hwf Heval.
      simpl in Heval.
      injection Heval as Heval.
      subst sn.
      exact Hwf.
    - intros p s0 sn Hwf Heval.
      simpl in Heval.
      destruct (SmallStepD.step s0 p) as [s1|] eqn:Hstep; try discriminate.
      exact (IHn' p s1 sn (step_preserves_top_pc_wf p s0 s1 Hwf Hstep) Heval).
  Qed.

  (* A variable not among [vars] is left untouched by [set_all]. *)
  Lemma set_all_not_in_preserves :
    forall (vars: list VarID.t) (vals: list D.value_t) (locals locals': LocalsD.t) (var: VarID.t),
      ~ In var vars ->
      LocalsD.set_all locals vars vals = Some locals' ->
      LocalsD.get locals' var = LocalsD.get locals var.
  Proof.
    induction vars as [| var0 vars' IH]; intros vals locals locals' var Hnotin Hset.
    - destruct vals as [| val0 vals']; simpl in Hset; try discriminate.
      injection Hset as Hset. subst locals'. reflexivity.
    - destruct vals as [| val0 vals']; simpl in Hset; try discriminate.
      assert (Hne : var <> var0) by (intro Heq; apply Hnotin; left; exact (eq_sym Heq)).
      assert (Hnotin' : ~ In var vars') by (intro Hin; apply Hnotin; right; exact Hin).
      rewrite (IH vals' (LocalsD.set locals var0 val0) locals' var Hnotin' Hset).
      unfold LocalsD.get, LocalsD.set.
      rewrite (proj2 (VarID.eqb_neq_false var var0) Hne).
      reflexivity.
  Qed.

  (* Given [NoDup vars], [set_all] assigns exactly the value at index
  [k] of [vals] to the variable at index [k] of [vars] -- no later
  assignment can overwrite it, since (by [NoDup]) that same variable
  never reappears further down the list. *)
  Lemma set_all_nth_error :
    forall (vars: list VarID.t) (vals: list D.value_t) (locals locals': LocalsD.t) (k: nat) (var: VarID.t) (val: D.value_t),
      NoDup vars ->
      LocalsD.set_all locals vars vals = Some locals' ->
      nth_error vars k = Some var ->
      nth_error vals k = Some val ->
      LocalsD.get locals' var = val.
  Proof.
    induction vars as [| var0 vars' IH]; intros vals locals locals' k var val Hnodup Hset Hvar Hval.
    - destruct k; simpl in Hvar; discriminate.
    - destruct vals as [| val0 vals']; simpl in Hset; try discriminate.
      inversion Hnodup as [| x0 l0 Hnotin Hnodup' Heqlist]; subst.
      destruct k as [| k'].
      + simpl in Hvar. injection Hvar as Hvar. subst var0.
        simpl in Hval. injection Hval as Hval. subst val0.
        rewrite (set_all_not_in_preserves vars' vals' (LocalsD.set locals var val) locals' var Hnotin Hset).
        unfold LocalsD.get, LocalsD.set.
        rewrite VarID.eqb_refl.
        reflexivity.
      + simpl in Hvar. simpl in Hval.
        exact (IH vals' (LocalsD.set locals var0 val0) locals' k' var val Hnodup' Hset Hvar Hval).
  Qed.

  (* [set_all] only ever succeeds when its two lists have the same
  length -- needed to know [phi_source]'s [List.combine out_vars
  in_sexprs] doesn't silently truncate either list short. *)
  Lemma set_all_length :
    forall (vars: list VarID.t) (vals: list D.value_t) (locals locals': LocalsD.t),
      LocalsD.set_all locals vars vals = Some locals' ->
      length vars = length vals.
  Proof.
    induction vars as [| var0 vars' IH]; intros vals locals locals' Hset.
    - destruct vals as [| val0 vals']; simpl in Hset; try discriminate.
      reflexivity.
    - destruct vals as [| val0 vals']; simpl in Hset; try discriminate.
      simpl. f_equal. exact (IH vals' (LocalsD.set locals var0 val0) locals' Hset).
  Qed.

  (* [phi_source]'s [None] case: [v] is not one of [b]'s phi-defined
  out-vars at all, so [set_all]/[set_all_not_in_preserves] applies
  directly. *)
  Lemma phi_source_none_not_in :
    forall (vars: list VarID.t) (exprs: list SimpleExprD.t) (v: VarID.t),
      length vars = length exprs ->
      List.find (fun ov => VarID.eqb (fst ov) v) (List.combine vars exprs) = None ->
      ~ In v vars.
  Proof.
    induction vars as [| v0 vars' IH]; intros exprs v Hlen Hfind.
    - intro Hin. destruct Hin.
    - destruct exprs as [| e0 exprs']; simpl in Hlen; try discriminate.
      simpl in Hfind.
      destruct (VarID.eqb v0 v) eqn:Heq.
      + discriminate Hfind.
      + intro Hin. destruct Hin as [Heq' | Hin].
        * subst v0. rewrite VarID.eqb_refl in Heq. discriminate Heq.
        * exact (IH exprs' v (eq_add_S _ _ Hlen) Hfind Hin).
  Qed.

  (* [phi_source]'s [Some e] case: [v] sits at some index [k] shared by
  both [out_vars] and [in_sexprs] -- letting [set_all_nth_error] pin
  down exactly what [v] resolves to. *)
  Lemma phi_source_some_nth_error :
    forall (vars: list VarID.t) (exprs: list SimpleExprD.t) (v: VarID.t) (e: SimpleExprD.t),
      length vars = length exprs ->
      List.find (fun ov => VarID.eqb (fst ov) v) (List.combine vars exprs) = Some (v, e) ->
      exists k, nth_error vars k = Some v /\ nth_error exprs k = Some e.
  Proof.
    induction vars as [| v0 vars' IH]; intros exprs v e Hlen Hfind.
    - simpl in Hfind. discriminate.
    - destruct exprs as [| e0 exprs']; simpl in Hlen; try discriminate.
      simpl in Hfind.
      destruct (VarID.eqb v0 v) eqn:Heq.
      + apply VarID.eqb_eq in Heq. subst v0.
        injection Hfind as Hfind1. subst e0.
        exists 0. simpl. split; reflexivity.
      + destruct (IH exprs' v e (eq_add_S _ _ Hlen) Hfind) as [k [Hk1 Hk2]].
        exists (S k). simpl. split; assumption.
  Qed.

  (* Decomposes a [frame :: rest] equality into its individual field
  equalities, plus the tail equality. Deliberately routed through
  generic (not literal-record) [fr1]/[fr2] so that [injection] always
  produces exactly the same, predictable two pieces internally --
  when applied to actual record literals at the call site, Coq's
  [injection] otherwise silently omits whichever fields happen to
  already be syntactically identical on both sides, making the number
  of resulting hypotheses depend on the specific values involved. *)
  Lemma frame_cons_eq_fields :
    forall (fr1 fr2: StackFrameD.t) (rest1 rest2: CallStackD.t),
      fr1 :: rest1 = fr2 :: rest2 ->
      StackFrameD.fname fr1 = StackFrameD.fname fr2 /\
      StackFrameD.locals fr1 = StackFrameD.locals fr2 /\
      StackFrameD.curr_bid fr1 = StackFrameD.curr_bid fr2 /\
      StackFrameD.pc fr1 = StackFrameD.pc fr2 /\
      rest1 = rest2.
  Proof.
    intros fr1 fr2 rest1 rest2 H.
    injection H as Hfr Hrest.
    subst rest2.
    rewrite Hfr.
    repeat split.
  Qed.

  (* Same idea, for comparing just the two heads (no tail equality
  needed) when the tails are already known to match. *)
  Lemma frame_eq_fields :
    forall (fr1 fr2: StackFrameD.t),
      fr1 = fr2 ->
      StackFrameD.fname fr1 = StackFrameD.fname fr2 /\
      StackFrameD.locals fr1 = StackFrameD.locals fr2 /\
      StackFrameD.curr_bid fr1 = StackFrameD.curr_bid fr2 /\
      StackFrameD.pc fr1 = StackFrameD.pc fr2.
  Proof.
    intros fr1 fr2 H. rewrite H. repeat split.
  Qed.

  (* Resolving the [k]-th simple expression of a list under a stack
  frame [sf] agrees, index by index, with [eval_sexpr]'s own result:
  a variable resolves via [sf]'s locals, a literal resolves to itself. *)
  Lemma eval_sexpr_nth_error :
    forall (l: list SimpleExprD.t) (sf: StackFrameD.t) (k: nat) (x: SimpleExprD.t),
      nth_error l k = Some x ->
      nth_error (SmallStepD.eval_sexpr l sf) k =
        Some (match x with inl var => LocalsD.get sf.(StackFrameD.locals) var | inr val => val end).
  Proof.
    induction l as [| x0 l' IH]; intros sf k x Hx.
    - destruct k; simpl in Hx; discriminate.
    - destruct k as [| k'].
      + simpl in Hx. injection Hx as Hx. subst x0.
        destruct x as [var | val]; reflexivity.
      + simpl in Hx.
        destruct x0 as [var0 | val0]; simpl; exact (IH sf k' x Hx).
  Qed.

  (* [eval_sexpr] produces one value per input expression. *)
  Lemma eval_sexpr_length :
    forall (l: list SimpleExprD.t) (sf: StackFrameD.t),
      length (SmallStepD.eval_sexpr l sf) = length l.
  Proof.
    induction l as [| x0 l' IH]; intros sf.
    - reflexivity.
    - destruct x0 as [var0 | val0]; simpl; f_equal; exact (IH sf).
  Qed.

  (* [const_sexprs] is defined mutually (co-inductively, for strict
  positivity) with [const_at_pc], but for a *fixed* finite list of
  simple expressions it can be unfolded by ordinary structural
  induction on the list itself, one [inversion] (single-step case
  analysis, not full coinductive recursion) at a time. This lets
  [const_at_pc_opcode]'s soundness proof reduce "all of [i]'s inputs are
  constant" down to "each input variable's own [const_at_pc] fact
  holds", leaving the per-variable reasoning (an application of the
  induction hypothesis, at the caller's specific point) as a parameter
  ([Hval]) rather than baking it in here. *)
  Lemma const_sexprs_eval_gen :
    forall (es: list SimpleExprD.t) (p: CFGProgD.t) (fn: FuncName.t) (bid: BlockID.t) (pc: nat)
           (cs: list D.value_t) (sf: StackFrameD.t),
      const_sexprs p fn bid pc es cs ->
      (forall (v: VarID.t) (c: D.value_t), const_at_pc p fn bid pc v c -> LocalsD.get sf.(StackFrameD.locals) v = c) ->
      SmallStepD.eval_sexpr es sf = cs.
  Proof.
    induction es as [| x es' IHes]; intros p fn bid pc cs sf Hsexprs Hval.
    - inversion Hsexprs; subst.
      reflexivity.
    - destruct x as [var | val].
      + inversion Hsexprs; subst.
        simpl.
        match goal with
        | H : const_at_pc _ _ _ _ ?v ?c |- _ => rewrite (Hval v c H)
        end.
        f_equal.
        match goal with
        | H : const_sexprs _ _ _ _ es' ?cs0 |- _ => exact (IHes p fn bid pc cs0 sf H Hval)
        end.
      + inversion Hsexprs; subst.
        simpl. f_equal.
        match goal with
        | H : const_sexprs _ _ _ _ es' ?cs0 |- _ => exact (IHes p fn bid pc cs0 sf H Hval)
        end.
  Qed.

  (* The one genuinely new reasoning step for [const_at_pc_entry]: a
  jump/cond-jump that lands us exactly on [bid1] at [pc=0] identifies
  [sf_mid]'s own current block as one of [bid1]'s predecessors, letting
  [Hpred1] be invoked; [top_pc_wf] then pins [sf_mid]'s own [pc] down to
  *exactly* [length(instructions b_mid)] (matching what [const_out]
  talks about), and [phi_source]/[set_all] are related via
  [phi_source_none_not_in]/[phi_source_some_nth_error]. Kept as its own
  top-level lemma (rather than inlined thrice, once per jump/cond-jump
  branch) so it can be stated and checked independently of the
  surrounding induction -- [IH] is simply its own parameter, with
  exactly the shape [const_at_pc_snd_gen]'s induction hypothesis has. *)
  Lemma const_at_pc_entry_jump_target :
    forall (n': nat)
           (IH : forall (m: nat), m < S n' ->
                   forall (p: CFGProgD.t) (fn: FuncName.t) (bid: BlockID.t) (at_pc: nat) (v: VarID.t) (c: D.value_t),
                     const_at_pc p fn bid at_pc v c ->
                     forall (s0 sn: StateD.t) (f: CFGFunD.t) (hl rest: CallStackD.t) (locals0 locals_n: LocalsD.t),
                       CFGProgD.get_func p fn = Some f ->
                       call_stack_wf p s0.(StateD.call_stack) ->
                       s0.(StateD.call_stack) = {| fname := fn; locals := locals0; curr_bid := f.(entry_bid); pc := 0 |} :: rest ->
                       SmallStepD.eval m s0 p = Some sn ->
                       sn.(StateD.call_stack) = hl ++ {| fname := fn; locals := locals_n; curr_bid := bid; pc := at_pc |} :: rest ->
                       LocalsD.get locals_n v = c)
           (p: CFGProgD.t) (fname1: FuncName.t) (bid1: BlockID.t) (v1: VarID.t) (c1: D.value_t) (b1: BlockD.t)
           (Hblock1 : CFGProgD.get_block p fname1 bid1 = Some b1)
           (Hnodup1 : NoDup (fst b1.(BlockD.phi_function)))
           (Hpred1 : forall pred_bid pred_b, is_predecessor_of p fname1 pred_bid bid1 pred_b ->
               (phi_source b1 pred_bid v1 = None /\ const_out p fname1 pred_bid v1 c1)
               \/ (exists v', phi_source b1 pred_bid v1 = Some (inl v') /\ const_out p fname1 pred_bid v' c1)
               \/ (exists val, phi_source b1 pred_bid v1 = Some (inr val) /\ c1 = val))
           (s0 s_mid: StateD.t) (f: CFGFunD.t) (rest: CallStackD.t) (locals0: LocalsD.t)
           (Hgetf : CFGProgD.get_func p fname1 = Some f)
           (Hwf0 : call_stack_wf p s0.(StateD.call_stack))
           (Hs0 : s0.(StateD.call_stack) = {| fname := fname1; locals := locals0; curr_bid := f.(entry_bid); pc := 0 |} :: rest)
           (Heval_mid : SmallStepD.eval n' s0 p = Some s_mid)
           (sf_mid: StackFrameD.t) (rsf_mid: CallStackD.t)
           (Hsmid : s_mid.(StateD.call_stack) = sf_mid :: rsf_mid)
           (Hpc_wf_mid : top_pc_wf p (sf_mid :: rsf_mid))
           (b_mid: BlockD.t)
           (Hblock_mid : CFGProgD.get_block p (StackFrameD.fname sf_mid) (StackFrameD.curr_bid sf_mid) = Some b_mid)
           (Hinstr_none : CFGProgD.get_instr p (StackFrameD.fname sf_mid) (StackFrameD.curr_bid sf_mid) (StackFrameD.pc sf_mid) = None)
           (next_bid: BlockID.t) (next_b_mid: BlockD.t) (in_sexprs: list SimpleExprD.t) (locals_mid': LocalsD.t)
           (Hfn_eq : StackFrameD.fname sf_mid = fname1)
           (Hbid_eq : next_bid = bid1)
           (Hrsf_eq : rsf_mid = rest)
           (Hnb_mid : CFGProgD.get_block p (StackFrameD.fname sf_mid) next_bid = Some next_b_mid)
           (Hphi_mid : snd (BlockD.phi_function next_b_mid) (StackFrameD.curr_bid sf_mid) = PhiInfoD.in_phi_info in_sexprs)
           (Hset_mid : LocalsD.set_all (StackFrameD.locals sf_mid) (fst (BlockD.phi_function next_b_mid)) (SmallStepD.eval_sexpr in_sexprs sf_mid) = Some locals_mid')
           (Hispred : is_predecessor_of p fname1 (StackFrameD.curr_bid sf_mid) bid1 b_mid),
      LocalsD.get locals_mid' v1 = c1.
  Proof.
    intros n' IH p fname1 bid1 v1 c1 b1 Hblock1 Hnodup1 Hpred1 s0 s_mid f rest locals0
           Hgetf Hwf0 Hs0 Heval_mid sf_mid rsf_mid Hsmid Hpc_wf_mid b_mid Hblock_mid Hinstr_none
           next_bid next_b_mid in_sexprs locals_mid' Hfn_eq Hbid_eq Hrsf_eq Hnb_mid Hphi_mid Hset_mid Hispred.
    subst next_bid.
    assert (Hnextb_eq : next_b_mid = b1).
    { rewrite Hfn_eq in Hnb_mid. rewrite Hblock1 in Hnb_mid. injection Hnb_mid as Hnb_mid. exact (eq_sym Hnb_mid). }
    subst next_b_mid.
    assert (Hblock_mid1 : CFGProgD.get_block p fname1 (StackFrameD.curr_bid sf_mid) = Some b_mid)
      by (rewrite <- Hfn_eq; exact Hblock_mid).
    assert (Hpc_eq_exact : StackFrameD.pc sf_mid = length (BlockD.instructions b_mid)).
    { assert (Hge : StackFrameD.pc sf_mid >= length (BlockD.instructions b_mid)).
      { unfold CFGProgD.get_instr in Hinstr_none. rewrite Hblock_mid in Hinstr_none.
        apply List.nth_error_None. exact Hinstr_none. }
      assert (Hle : StackFrameD.pc sf_mid <= length (BlockD.instructions b_mid))
        by exact (Hpc_wf_mid b_mid Hblock_mid).
      lia. }
    assert (Hunfold_phi : phi_source b1 (StackFrameD.curr_bid sf_mid) v1 =
              match List.find (fun ov => VarID.eqb (fst ov) v1) (List.combine (fst (BlockD.phi_function b1)) in_sexprs) with
              | Some (_, e) => Some e
              | None => None
              end)
      by (unfold phi_source; rewrite Hphi_mid; reflexivity).
    assert (Hlen_mid : length (fst (BlockD.phi_function b1)) = length in_sexprs).
    { rewrite <- (eval_sexpr_length in_sexprs sf_mid).
      exact (set_all_length (fst (BlockD.phi_function b1)) (SmallStepD.eval_sexpr in_sexprs sf_mid)
               (StackFrameD.locals sf_mid) locals_mid' Hset_mid). }
    assert (Hlt : n' < S n') by lia.
    pose proof (Hpred1 (StackFrameD.curr_bid sf_mid) b_mid Hispred) as Hpred1'.
    destruct Hpred1' as
      [[Hphi_none Hco] | [[v' [Hphi_var Hco]] | [val [Hphi_val Hc_eq]]]].
    - (* None: v1 carries over unchanged from the predecessor's own exit *)
      rewrite Hunfold_phi in Hphi_none.
      destruct (List.find (fun ov => VarID.eqb (fst ov) v1) (List.combine (fst (BlockD.phi_function b1)) in_sexprs))
        as [[v'' e'']|] eqn:Hfind_mid; try discriminate Hphi_none.
      assert (Hnotin : ~ In v1 (fst (BlockD.phi_function b1)))
        by exact (phi_source_none_not_in (fst (BlockD.phi_function b1)) in_sexprs v1 Hlen_mid Hfind_mid).
      assert (Hval_eq : LocalsD.get locals_mid' v1 = LocalsD.get (StackFrameD.locals sf_mid) v1)
        by exact (set_all_not_in_preserves (fst (BlockD.phi_function b1)) (SmallStepD.eval_sexpr in_sexprs sf_mid)
                    (StackFrameD.locals sf_mid) locals_mid' v1 Hnotin Hset_mid).
      rewrite Hval_eq.
      pose proof (const_out_inv p fname1 (StackFrameD.curr_bid sf_mid) v1 c1 Hco) as Hco_inv.
      destruct Hco_inv as [b_co [Hblock_co Hat_co]].
      rewrite Hblock_co in Hblock_mid1. injection Hblock_mid1 as Hblock_mid1. subst b_co.
      assert (Hsmid_shape : s_mid.(StateD.call_stack) = [] ++
                {| fname := fname1; locals := StackFrameD.locals sf_mid;
                   curr_bid := StackFrameD.curr_bid sf_mid; pc := length (BlockD.instructions b_mid) |} :: rest).
      { simpl. rewrite Hsmid, <- Hrsf_eq, <- Hfn_eq, <- Hpc_eq_exact. destruct sf_mid; reflexivity. }
      exact (IH n' Hlt p fname1 (StackFrameD.curr_bid sf_mid) (length (BlockD.instructions b_mid)) v1 c1 Hat_co
               s0 s_mid f [] rest locals0 (StackFrameD.locals sf_mid) Hgetf Hwf0 Hs0 Heval_mid Hsmid_shape).
    - (* Some (inl v'): v1 takes v''s value at the predecessor's own exit *)
      rewrite Hunfold_phi in Hphi_var.
      destruct (List.find (fun ov => VarID.eqb (fst ov) v1) (List.combine (fst (BlockD.phi_function b1)) in_sexprs))
        as [[v'' e'']|] eqn:Hfind_mid; try discriminate Hphi_var.
      injection Hphi_var as Hphi_var.
      destruct (List.find_some _ _ Hfind_mid) as [_ Hpred_true].
      simpl in Hpred_true. apply VarID.eqb_eq in Hpred_true. subst v''.
      subst e''.
      destruct (phi_source_some_nth_error (fst (BlockD.phi_function b1)) in_sexprs v1 (inl v') Hlen_mid Hfind_mid)
        as [k [Hk_var Hk_expr]].
      assert (Hinput_val : nth_error (SmallStepD.eval_sexpr in_sexprs sf_mid) k = Some (LocalsD.get (StackFrameD.locals sf_mid) v'))
        by exact (eval_sexpr_nth_error in_sexprs sf_mid k (inl v') Hk_expr).
      assert (Hval_eq : LocalsD.get locals_mid' v1 = LocalsD.get (StackFrameD.locals sf_mid) v')
        by exact (set_all_nth_error (fst (BlockD.phi_function b1)) (SmallStepD.eval_sexpr in_sexprs sf_mid)
                    (StackFrameD.locals sf_mid) locals_mid' k v1 _ Hnodup1 Hset_mid Hk_var Hinput_val).
      rewrite Hval_eq.
      pose proof (const_out_inv p fname1 (StackFrameD.curr_bid sf_mid) v' c1 Hco) as Hco_inv.
      destruct Hco_inv as [b_co [Hblock_co Hat_co]].
      rewrite Hblock_co in Hblock_mid1. injection Hblock_mid1 as Hblock_mid1. subst b_co.
      assert (Hsmid_shape : s_mid.(StateD.call_stack) = [] ++
                {| fname := fname1; locals := StackFrameD.locals sf_mid;
                   curr_bid := StackFrameD.curr_bid sf_mid; pc := length (BlockD.instructions b_mid) |} :: rest).
      { simpl. rewrite Hsmid, <- Hrsf_eq, <- Hfn_eq, <- Hpc_eq_exact. destruct sf_mid; reflexivity. }
      exact (IH n' Hlt p fname1 (StackFrameD.curr_bid sf_mid) (length (BlockD.instructions b_mid)) v' c1 Hat_co
               s0 s_mid f [] rest locals0 (StackFrameD.locals sf_mid) Hgetf Hwf0 Hs0 Heval_mid Hsmid_shape).
    - (* Some (inr val): v1 is a phi-defined literal constant, no recursion needed *)
      rewrite Hunfold_phi in Hphi_val.
      destruct (List.find (fun ov => VarID.eqb (fst ov) v1) (List.combine (fst (BlockD.phi_function b1)) in_sexprs))
        as [[v'' e'']|] eqn:Hfind_mid; try discriminate Hphi_val.
      injection Hphi_val as Hphi_val.
      destruct (List.find_some _ _ Hfind_mid) as [_ Hpred_true].
      simpl in Hpred_true. apply VarID.eqb_eq in Hpred_true. subst v''.
      subst e''.
      destruct (phi_source_some_nth_error (fst (BlockD.phi_function b1)) in_sexprs v1 (inr val) Hlen_mid Hfind_mid)
        as [k [Hk_var Hk_expr]].
      assert (Hinput_val : nth_error (SmallStepD.eval_sexpr in_sexprs sf_mid) k = Some val)
        by exact (eval_sexpr_nth_error in_sexprs sf_mid k (inr val) Hk_expr).
      assert (Hval_eq : LocalsD.get locals_mid' v1 = val)
        by exact (set_all_nth_error (fst (BlockD.phi_function b1)) (SmallStepD.eval_sexpr in_sexprs sf_mid)
                    (StackFrameD.locals sf_mid) locals_mid' k v1 val Hnodup1 Hset_mid Hk_var Hinput_val).
      rewrite Hval_eq, Hc_eq. reflexivity.
  Qed.

  Lemma const_at_pc_snd_gen :
    forall (n: nat) (p: CFGProgD.t) (fn: FuncName.t) (bid: BlockID.t) (at_pc: nat) (v: VarID.t) (c: D.value_t),
      const_at_pc p fn bid at_pc v c ->
      forall (s0 sn: StateD.t) (f: CFGFunD.t) (hl rest: CallStackD.t) (locals0 locals_n: LocalsD.t),
        CFGProgD.get_func p fn = Some f ->
        (* [s0] -- the state right when [fn] starts -- must itself be a
        well-formed configuration: whoever called [fn] (and whoever
        called *them*, and so on down [rest]) really is sitting at a
        call instruction. This is a natural assumption for any state
        that actually arises from running the program; it is not
        implied by [step] alone (see [frame_pc_is_call]'s comment). *)
        call_stack_wf p s0.(StateD.call_stack) ->
        s0.(StateD.call_stack) = {| fname := fn; locals := locals0; curr_bid := f.(entry_bid); pc := 0 |} :: rest ->
        SmallStepD.eval n s0 p = Some sn ->
        sn.(StateD.call_stack) = hl ++ {| fname := fn; locals := locals_n; curr_bid := bid; pc := at_pc |} :: rest ->
        LocalsD.get locals_n v = c.
  Proof.
    induction n as [n IH] using lt_wf_ind.
    intros p fn bid at_pc v c Hconst s0 sn f hl rest locals0 locals_n Hgetf Hwf0 Hs0 Heval Hsn.
    destruct hl as [| a hl'].
    - (* hl = [] : our frame is directly on top of rest; dispatch on
      how [const_at_pc] was derived. *)
      simpl in Hsn.
      destruct Hconst as
        [ fname1 bid1 v1 c1 Hin1
        | fname2 bid2 pc2 b2 i2 v2 c2 Hblock2 Hnth2 Hnotin2 Hprev2
        | fname3 bid3 pc3 b3 i3 v3 c3 k3 x3 Hblock3 Hnth3 Hop3 Hout3 Hin3 Hdisj3
        | fname4 bid4 pc4 b4 i4 opcode4 v4 c4 k4 ci4 rv4 st4 Hblock4 Hnth4 Hop4 Hindep4 Hsexprs4 Hexec4 Hout4 Hres4
        ].
      + (* const_at_pc_entry: the only genuinely cross-block case --
        reaching [bid1] at [pc = 0] means the last step was a
        jump/cond-jump landing on it from one of its predecessors (a
        pushed call is ruled out via [Hne1]: fresh frames start at
        their *own* function's entry, not [bid1]; ordinary instruction
        execution/return are ruled out since they always set pc to a
        successor, never [0]), so [const_at_pc_entry_jump_target]
        handles all three (Jump/ConditionalJump-true/
        ConditionalJump-false) branches identically. *)
        destruct Hin1 as [fname1 f1 bid1 b1 v1 c1 Hgetf1 Hne1 Hblock1 Hnodup1 Hpred1].
        assert (Hf1_eq : f1 = f) by (rewrite Hgetf in Hgetf1; injection Hgetf1 as Hgetf1; exact (eq_sym Hgetf1)).
        subst f1.
        destruct n as [| n'].
        * (* n = 0: sn = s0, but bid1 <> entry_bid f *)
          exfalso.
          simpl in Heval. injection Heval as Heval. subst sn.
          rewrite Hs0 in Hsn.
          try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [_ [_ [Hbid_eq [_ _]]]].
          exact (Hne1 (eq_sym Hbid_eq)).
        * (* n = S n' *)
          assert (Hlt : n' < S n') by lia.
          destruct (eval_split_last n' p s0 sn Heval) as [s_mid [Heval_mid Hstep_mid]].
          assert (Hpc_wf0 : top_pc_wf p s0.(StateD.call_stack)).
          { rewrite Hs0. simpl. intros b' Hb'. lia. }
          assert (Hpcwf_mid : top_pc_wf p s_mid.(StateD.call_stack))
            by exact (eval_preserves_top_pc_wf n' p s0 s_mid Hpc_wf0 Heval_mid).
          destruct (s_mid.(StateD.call_stack)) as [| sf_mid rsf_mid] eqn:Hsmid.
          -- exfalso.
             unfold SmallStepD.step in Hstep_mid.
             destruct (StateD.status s_mid); try discriminate.
             unfold SmallStepD.get_next_instr in Hstep_mid.
             rewrite Hsmid in Hstep_mid.
             injection Hstep_mid as Hstep_mid.
             subst sn.
             unfold SmallStepD.handle_block_exit in Hsn.
             rewrite Hsmid in Hsn.
             unfold SmallStepD.error in Hsn.
             simpl in Hsn.
             rewrite Hsmid in Hsn.
             discriminate Hsn.
          -- assert (Hih_unchanged :
                       StackFrameD.fname sf_mid = fname1 -> StackFrameD.locals sf_mid = locals_n ->
                       StackFrameD.curr_bid sf_mid = bid1 -> StackFrameD.pc sf_mid = 0 ->
                       rsf_mid = rest ->
                       LocalsD.get locals_n v1 = c1).
             { intros Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq.
               assert (Hsf_eq : sf_mid = {| fname := fname1; locals := locals_n; curr_bid := bid1; pc := 0 |}).
               { destruct sf_mid as [f0 l0 cb0 p0]. simpl in *. subst. reflexivity. }
               subst sf_mid rsf_mid.
               exact (IH n' Hlt p fname1 bid1 0 v1 c1
                        (const_at_pc_entry p fname1 bid1 v1 c1
                           (const_in_merge p fname1 f bid1 b1 v1 c1 Hgetf1 Hne1 Hblock1 Hnodup1 Hpred1))
                        s0 s_mid f [] rest locals0 locals_n Hgetf Hwf0 Hs0 Heval_mid Hsmid). }
             unfold SmallStepD.step in Hstep_mid.
             destruct (StateD.status s_mid) eqn:Hstatus_mid; try discriminate.
             unfold SmallStepD.get_next_instr in Hstep_mid.
             rewrite Hsmid in Hstep_mid.
             destruct (CFGProgD.get_instr p (StackFrameD.fname sf_mid) (StackFrameD.curr_bid sf_mid) (StackFrameD.pc sf_mid))
               as [instr_mid|] eqn:Hinstr_mid.
             ++ (* execute_instr fired *)
                injection Hstep_mid as Hstep_mid.
                subst sn.
                unfold SmallStepD.execute_instr in Hsn.
                rewrite Hsmid in Hsn.
                destruct (InstrD.op instr_mid) as [[callee_mid | opcode_mid] | aux_mid] eqn:Hop_mid.
                ** (* function call: a fresh frame starts at its own entry, not bid1 <> entry_bid *)
                   unfold SmallStepD.execute_func in Hsn.
                   destruct (CFGProgD.get_func p callee_mid) as [func_mid|] eqn:Hfunc_mid.
                   --- destruct (LocalsD.set_all LocalsD.empty (CFGFunD.args func_mid)
                                   (SmallStepD.eval_sexpr (InstrD.input instr_mid) sf_mid)) as [locals_mid'|] eqn:Hset_mid.
                       +++ exfalso. simpl in Hsn.
                           try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [_ [Hbid_eq [_ _]]]].
                           simpl in Hfn_eq, Hbid_eq.
                           assert (Hfunc_eq : func_mid = f).
                           { rewrite Hfn_eq in Hfunc_mid. rewrite Hgetf in Hfunc_mid. injection Hfunc_mid as Hfunc_mid.
                             exact (eq_sym Hfunc_mid). }
                           subst func_mid.
                           exact (Hne1 (eq_sym Hbid_eq)).
                       +++ simpl in Hsn.
                           try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                           exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                   --- simpl in Hsn.
                       try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                       exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                ** (* opcode: success always sets pc := pc_mid + 1 <> 0 *)
                   unfold SmallStepD.execute_opcode in Hsn.
                   destruct (D.execute_opcode (StateD.dialect_state s_mid) opcode_mid
                               (SmallStepD.eval_sexpr (InstrD.input instr_mid) sf_mid))
                     as [[out_vals dialect_state'] status'].
                   unfold SmallStepD.execute_assignment in Hsn.
                   destruct (LocalsD.set_all (StackFrameD.locals sf_mid) (InstrD.output instr_mid) out_vals)
                     as [locals_mid'|] eqn:Hset_mid.
                   --- exfalso. simpl in Hsn.
                       try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [_ [_ [_ [Hpc_eq _]]]].
                       simpl in Hpc_eq. lia.
                   --- simpl in Hsn.
                       try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                       exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                ** (* assign: same reasoning as opcode *)
                   destruct aux_mid.
                   unfold SmallStepD.execute_assignment in Hsn.
                   destruct (LocalsD.set_all (StackFrameD.locals sf_mid) (InstrD.output instr_mid)
                               (SmallStepD.eval_sexpr (InstrD.input instr_mid) sf_mid)) as [locals_mid'|] eqn:Hset_mid.
                   --- exfalso. simpl in Hsn.
                       try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [_ [_ [_ [Hpc_eq _]]]].
                       simpl in Hpc_eq. lia.
                   --- simpl in Hsn.
                       try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                       exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
             ++ (* handle_block_exit fired *)
                injection Hstep_mid as Hstep_mid.
                subst sn.
                unfold SmallStepD.handle_block_exit in Hsn.
                rewrite Hsmid in Hsn.
                destruct (CFGProgD.get_block p (StackFrameD.fname sf_mid) (StackFrameD.curr_bid sf_mid)) as [b_mid|] eqn:Hblock_mid.
                ** destruct (BlockD.exit_info b_mid) as [cond_var_mid bidt_mid bidf_mid | jbid_mid | ret_sexprs_mid | ] eqn:Hexit_mid.
                   --- (* ConditionalJump: the target scenario *)
                       unfold SmallStepD.handle_cond_jump in Hsn.
                       simpl in Hsn.
                       destruct (D.is_true_value (LocalsD.get (StackFrameD.locals sf_mid) cond_var_mid)) eqn:Hcond_mid.
                       +++ unfold SmallStepD.handle_jump in Hsn.
                           destruct (CFGProgD.get_block p (StackFrameD.fname sf_mid) bidt_mid) as [next_b_mid|] eqn:Hnb_mid.
                           *** unfold SmallStepD.handle_jump_aux in Hsn.
                               destruct (snd (BlockD.phi_function next_b_mid) (StackFrameD.curr_bid sf_mid)) eqn:Hphi_mid.
                               destruct (LocalsD.set_all (StackFrameD.locals sf_mid) (fst (BlockD.phi_function next_b_mid))
                                           (SmallStepD.eval_sexpr in_sexprs sf_mid)) as [locals_mid'|] eqn:Hset_mid.
                               ---- simpl in Hsn.
                                    try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                                    simpl in Hfn_eq, Hloc_eq, Hbid_eq.
                                    rewrite <- Hloc_eq.
                                    assert (Hispred : is_predecessor_of p fname1 (StackFrameD.curr_bid sf_mid) bid1 b_mid).
                                    { split.
                                      - rewrite <- Hfn_eq. exact Hblock_mid.
                                      - rewrite Hexit_mid. simpl. left. exact Hbid_eq. }
                                    exact (const_at_pc_entry_jump_target n' IH p fname1 bid1 v1 c1 b1 Hblock1 Hnodup1 Hpred1
                                             s0 s_mid f rest locals0 Hgetf Hwf0 Hs0 Heval_mid sf_mid rsf_mid Hsmid Hpcwf_mid
                                             b_mid Hblock_mid Hinstr_mid bidt_mid next_b_mid in_sexprs locals_mid'
                                             Hfn_eq Hbid_eq Hrsf_eq Hnb_mid Hphi_mid Hset_mid Hispred).
                               ---- simpl in Hsn.
                                    try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                                    exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                           *** simpl in Hsn.
                               try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                               exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                       +++ unfold SmallStepD.handle_jump in Hsn.
                           destruct (CFGProgD.get_block p (StackFrameD.fname sf_mid) bidf_mid) as [next_b_mid|] eqn:Hnb_mid.
                           *** unfold SmallStepD.handle_jump_aux in Hsn.
                               destruct (snd (BlockD.phi_function next_b_mid) (StackFrameD.curr_bid sf_mid)) eqn:Hphi_mid.
                               destruct (LocalsD.set_all (StackFrameD.locals sf_mid) (fst (BlockD.phi_function next_b_mid))
                                           (SmallStepD.eval_sexpr in_sexprs sf_mid)) as [locals_mid'|] eqn:Hset_mid.
                               ---- simpl in Hsn.
                                    try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                                    simpl in Hfn_eq, Hloc_eq, Hbid_eq.
                                    rewrite <- Hloc_eq.
                                    assert (Hispred : is_predecessor_of p fname1 (StackFrameD.curr_bid sf_mid) bid1 b_mid).
                                    { split.
                                      - rewrite <- Hfn_eq. exact Hblock_mid.
                                      - rewrite Hexit_mid. simpl. right. exact Hbid_eq. }
                                    exact (const_at_pc_entry_jump_target n' IH p fname1 bid1 v1 c1 b1 Hblock1 Hnodup1 Hpred1
                                             s0 s_mid f rest locals0 Hgetf Hwf0 Hs0 Heval_mid sf_mid rsf_mid Hsmid Hpcwf_mid
                                             b_mid Hblock_mid Hinstr_mid bidf_mid next_b_mid in_sexprs locals_mid'
                                             Hfn_eq Hbid_eq Hrsf_eq Hnb_mid Hphi_mid Hset_mid Hispred).
                               ---- simpl in Hsn.
                                    try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                                    exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                           *** simpl in Hsn.
                               try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                               exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                   --- (* Jump: the target scenario *)
                       unfold SmallStepD.handle_jump in Hsn.
                       destruct (CFGProgD.get_block p (StackFrameD.fname sf_mid) jbid_mid) as [next_b_mid|] eqn:Hnb_mid.
                       +++ unfold SmallStepD.handle_jump_aux in Hsn.
                           destruct (snd (BlockD.phi_function next_b_mid) (StackFrameD.curr_bid sf_mid)) eqn:Hphi_mid.
                           destruct (LocalsD.set_all (StackFrameD.locals sf_mid) (fst (BlockD.phi_function next_b_mid))
                                       (SmallStepD.eval_sexpr in_sexprs sf_mid)) as [locals_mid'|] eqn:Hset_mid.
                           *** simpl in Hsn.
                               try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                               simpl in Hfn_eq, Hloc_eq, Hbid_eq.
                               rewrite <- Hloc_eq.
                               assert (Hispred : is_predecessor_of p fname1 (StackFrameD.curr_bid sf_mid) bid1 b_mid).
                               { split.
                                 - rewrite <- Hfn_eq. exact Hblock_mid.
                                 - rewrite Hexit_mid. exact Hbid_eq. }
                               exact (const_at_pc_entry_jump_target n' IH p fname1 bid1 v1 c1 b1 Hblock1 Hnodup1 Hpred1
                                        s0 s_mid f rest locals0 Hgetf Hwf0 Hs0 Heval_mid sf_mid rsf_mid Hsmid Hpcwf_mid
                                        b_mid Hblock_mid Hinstr_mid jbid_mid next_b_mid in_sexprs locals_mid'
                                        Hfn_eq Hbid_eq Hrsf_eq Hnb_mid Hphi_mid Hset_mid Hispred).
                           *** simpl in Hsn.
                               try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                               exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                       +++ simpl in Hsn.
                           try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                           exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                   --- (* ReturnBlock: success always sets pc := pc(sf2) + 1 <> 0 *)
                       unfold SmallStepD.handle_return in Hsn.
                       destruct rsf_mid as [| sf2 rsf2] eqn:Hrsfmid.
                       +++ simpl in Hsn.
                           try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                           exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                       +++ destruct (CFGProgD.get_block p (StackFrameD.fname sf2) (StackFrameD.curr_bid sf2)) as [b2'|] eqn:Hblock2'.
                           *** destruct (List.nth_error (BlockD.instructions b2') (StackFrameD.pc sf2)) as [instr2'|] eqn:Hnth2'.
                               ---- unfold SmallStepD.execute_assignment in Hsn.
                                    destruct (LocalsD.set_all (StackFrameD.locals sf2) (InstrD.output instr2')
                                                (SmallStepD.eval_sexpr ret_sexprs_mid sf_mid)) as [locals2'|] eqn:Hset2.
                                    ++++ exfalso. simpl in Hsn.
                                         try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [_ [_ [_ [Hpc_eq _]]]].
                                         simpl in Hpc_eq. lia.
                                    ++++ simpl in Hsn.
                                         try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                                         exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                               ---- simpl in Hsn.
                                    try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                                    exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                           *** simpl in Hsn.
                               try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                               exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                   --- (* Terminate: frame untouched, only status changes *)
                       unfold SmallStepD.handle_terminate in Hsn.
                       simpl in Hsn.
                       try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                       exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                ** (* block not found: error, unchanged *)
                   simpl in Hsn.
                   try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                   exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
      + (* const_at_pc_unaffected: symmetric to [const_at_pc_assign]'s
        skeleton below, except that the executed instruction can be of
        *any* kind (call/opcode/assign) -- all three are legitimate
        "target scenario" branches here (unlike [const_at_pc_assign],
        where non-ASSIGN kinds are excluded via [Hop3]), since all that
        matters is that [v2] itself is not among the instruction's
        outputs ([set_all_not_in_preserves]). *)
        destruct n as [| n'].
        * (* n = 0: sn = s0, but pc mismatch (0 vs S pc2) *)
          simpl in Heval. injection Heval as Heval. subst sn.
          rewrite Hs0 in Hsn.
          try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [_ [_ [_ [Hpc_eq _]]]].
          discriminate Hpc_eq.
        * (* n = S n' *)
          assert (Hlt : n' < S n') by lia.
          destruct (eval_split_last n' p s0 sn Heval) as [s_mid [Heval_mid Hstep_mid]].
          assert (Hwf_mid : call_stack_wf p s_mid.(StateD.call_stack))
            by exact (eval_preserves_call_stack_wf n' p s0 s_mid Hwf0 Heval_mid).
          destruct (s_mid.(StateD.call_stack)) as [| sf_mid rsf_mid] eqn:Hsmid.
          -- (* s_mid.call_stack = nil: impossible *)
             exfalso.
             unfold SmallStepD.step in Hstep_mid.
             destruct (StateD.status s_mid); try discriminate.
             unfold SmallStepD.get_next_instr in Hstep_mid.
             rewrite Hsmid in Hstep_mid.
             injection Hstep_mid as Hstep_mid.
             subst sn.
             unfold SmallStepD.handle_block_exit in Hsn.
             rewrite Hsmid in Hsn.
             unfold SmallStepD.error in Hsn.
             simpl in Hsn.
             rewrite Hsmid in Hsn.
             discriminate Hsn.
          -- assert (Hih_unchanged :
                       StackFrameD.fname sf_mid = fname2 -> StackFrameD.locals sf_mid = locals_n ->
                       StackFrameD.curr_bid sf_mid = bid2 -> StackFrameD.pc sf_mid = S pc2 ->
                       rsf_mid = rest ->
                       LocalsD.get locals_n v2 = c2).
             { intros Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq.
               assert (Hsf_eq : sf_mid = {| fname := fname2; locals := locals_n; curr_bid := bid2; pc := S pc2 |}).
               { destruct sf_mid as [f0 l0 cb0 p0]. simpl in *. subst. reflexivity. }
               subst sf_mid rsf_mid.
               exact (IH n' Hlt p fname2 bid2 (S pc2) v2 c2
                        (const_at_pc_unaffected p fname2 bid2 pc2 b2 i2 v2 c2 Hblock2 Hnth2 Hnotin2 Hprev2)
                        s0 s_mid f [] rest locals0 locals_n Hgetf Hwf0 Hs0 Heval_mid Hsmid). }
             unfold SmallStepD.step in Hstep_mid.
             destruct (StateD.status s_mid) eqn:Hstatus_mid; try discriminate.
             unfold SmallStepD.get_next_instr in Hstep_mid.
             rewrite Hsmid in Hstep_mid.
             destruct (CFGProgD.get_instr p (StackFrameD.fname sf_mid) (StackFrameD.curr_bid sf_mid) (StackFrameD.pc sf_mid))
               as [instr_mid|] eqn:Hinstr_mid.
             ++ (* execute_instr fired *)
                injection Hstep_mid as Hstep_mid.
                subst sn.
                unfold SmallStepD.execute_instr in Hsn.
                rewrite Hsmid in Hsn.
                destruct (InstrD.op instr_mid) as [[callee_mid | opcode_mid] | aux_mid] eqn:Hop_mid.
                ** (* function call: a successful push always has pc = 0 <> S pc2 *)
                   unfold SmallStepD.execute_func in Hsn.
                   destruct (CFGProgD.get_func p callee_mid) as [func_mid|] eqn:Hfunc_mid.
                   --- destruct (LocalsD.set_all LocalsD.empty (CFGFunD.args func_mid)
                                   (SmallStepD.eval_sexpr (InstrD.input instr_mid) sf_mid)) as [locals_mid'|] eqn:Hset_mid.
                       +++ exfalso. simpl in Hsn.
                           try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [_ [_ [_ [Hpc_eq _]]]].
                           discriminate Hpc_eq.
                       +++ simpl in Hsn.
                           try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                           exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                   --- simpl in Hsn.
                       try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                       exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                ** (* opcode: a legitimate target scenario, [v2] just isn't among its outputs *)
                   unfold SmallStepD.execute_opcode in Hsn.
                   destruct (D.execute_opcode (StateD.dialect_state s_mid) opcode_mid
                               (SmallStepD.eval_sexpr (InstrD.input instr_mid) sf_mid))
                     as [[out_vals dialect_state'] status'].
                   unfold SmallStepD.execute_assignment in Hsn.
                   destruct (LocalsD.set_all (StackFrameD.locals sf_mid) (InstrD.output instr_mid) out_vals)
                     as [locals_mid'|] eqn:Hset_mid.
                   --- simpl in Hsn.
                       try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                       simpl in Hfn_eq, Hloc_eq, Hbid_eq, Hpc_eq. assert (Hpc_eq' : StackFrameD.pc sf_mid = pc2) by lia.
                       assert (Hinstr_eq : CFGProgD.get_instr p fname2 bid2 pc2 = Some instr_mid).
                       { rewrite <- Hfn_eq, <- Hbid_eq, <- Hpc_eq'. exact Hinstr_mid. }
                       assert (Hget_i2 : CFGProgD.get_instr p fname2 bid2 pc2 = Some i2).
                       { unfold CFGProgD.get_instr. rewrite Hblock2. exact Hnth2. }
                       rewrite Hget_i2 in Hinstr_eq.
                       injection Hinstr_eq as Hinstr_eq.
                       subst instr_mid.
                       rewrite <- Hloc_eq.
                       assert (Hval2 : LocalsD.get locals_mid' v2 = LocalsD.get (StackFrameD.locals sf_mid) v2)
                         by exact (set_all_not_in_preserves (InstrD.output i2) out_vals
                                     (StackFrameD.locals sf_mid) locals_mid' v2 Hnotin2 Hset_mid).
                       rewrite Hval2.
                       assert (Hsmid_shape : s_mid.(StateD.call_stack) = [] ++ {| fname := fname2; locals := StackFrameD.locals sf_mid; curr_bid := bid2; pc := pc2 |} :: rest).
                       { simpl. rewrite Hsmid, <- Hrsf_eq.
                         rewrite <- Hfn_eq, <- Hbid_eq, <- Hpc_eq'.
                         destruct sf_mid; reflexivity. }
                       exact (IH n' Hlt p fname2 bid2 pc2 v2 c2 Hprev2
                                s0 s_mid f [] rest locals0 (StackFrameD.locals sf_mid) Hgetf Hwf0 Hs0 Heval_mid Hsmid_shape).
                   --- simpl in Hsn.
                       try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                       exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                ** (* assign: same reasoning as opcode above *)
                   destruct aux_mid.
                   unfold SmallStepD.execute_assignment in Hsn.
                   destruct (LocalsD.set_all (StackFrameD.locals sf_mid) (InstrD.output instr_mid)
                               (SmallStepD.eval_sexpr (InstrD.input instr_mid) sf_mid)) as [locals_mid'|] eqn:Hset_mid.
                   --- simpl in Hsn.
                       try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                       simpl in Hfn_eq, Hloc_eq, Hbid_eq, Hpc_eq. assert (Hpc_eq' : StackFrameD.pc sf_mid = pc2) by lia.
                       assert (Hinstr_eq : CFGProgD.get_instr p fname2 bid2 pc2 = Some instr_mid).
                       { rewrite <- Hfn_eq, <- Hbid_eq, <- Hpc_eq'. exact Hinstr_mid. }
                       assert (Hget_i2 : CFGProgD.get_instr p fname2 bid2 pc2 = Some i2).
                       { unfold CFGProgD.get_instr. rewrite Hblock2. exact Hnth2. }
                       rewrite Hget_i2 in Hinstr_eq.
                       injection Hinstr_eq as Hinstr_eq.
                       subst instr_mid.
                       rewrite <- Hloc_eq.
                       assert (Hval2 : LocalsD.get locals_mid' v2 = LocalsD.get (StackFrameD.locals sf_mid) v2)
                         by exact (set_all_not_in_preserves (InstrD.output i2) (SmallStepD.eval_sexpr (InstrD.input i2) sf_mid)
                                     (StackFrameD.locals sf_mid) locals_mid' v2 Hnotin2 Hset_mid).
                       rewrite Hval2.
                       assert (Hsmid_shape : s_mid.(StateD.call_stack) = [] ++ {| fname := fname2; locals := StackFrameD.locals sf_mid; curr_bid := bid2; pc := pc2 |} :: rest).
                       { simpl. rewrite Hsmid, <- Hrsf_eq.
                         rewrite <- Hfn_eq, <- Hbid_eq, <- Hpc_eq'.
                         destruct sf_mid; reflexivity. }
                       exact (IH n' Hlt p fname2 bid2 pc2 v2 c2 Hprev2
                                s0 s_mid f [] rest locals0 (StackFrameD.locals sf_mid) Hgetf Hwf0 Hs0 Heval_mid Hsmid_shape).
                   --- simpl in Hsn.
                       try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                       exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
             ++ (* handle_block_exit fired *)
                injection Hstep_mid as Hstep_mid.
                subst sn.
                unfold SmallStepD.handle_block_exit in Hsn.
                rewrite Hsmid in Hsn.
                destruct (CFGProgD.get_block p (StackFrameD.fname sf_mid) (StackFrameD.curr_bid sf_mid)) as [b_mid|] eqn:Hblock_mid.
                ** destruct (BlockD.exit_info b_mid) as [cond_var_mid bidt_mid bidf_mid | jbid_mid | ret_sexprs_mid | ] eqn:Hexit_mid.
                   --- (* ConditionalJump: a successful jump always sets pc := 0 <> S pc2 *)
                       unfold SmallStepD.handle_cond_jump in Hsn.
                       simpl in Hsn.
                       destruct (D.is_true_value (LocalsD.get (StackFrameD.locals sf_mid) cond_var_mid)) eqn:Hcond_mid.
                       +++ unfold SmallStepD.handle_jump in Hsn.
                           destruct (CFGProgD.get_block p (StackFrameD.fname sf_mid) bidt_mid) as [next_b_mid|] eqn:Hnb_mid.
                           *** unfold SmallStepD.handle_jump_aux in Hsn.
                               destruct (snd (BlockD.phi_function next_b_mid) (StackFrameD.curr_bid sf_mid)) eqn:Hphi_mid.
                               destruct (LocalsD.set_all (StackFrameD.locals sf_mid) (fst (BlockD.phi_function next_b_mid))
                                           (SmallStepD.eval_sexpr in_sexprs sf_mid)) as [locals_mid'|] eqn:Hset_mid.
                               ---- exfalso. simpl in Hsn.
                                    try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [_ [_ [_ [Hpc_eq _]]]].
                                    discriminate Hpc_eq.
                               ---- simpl in Hsn.
                                    try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                                    exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                           *** simpl in Hsn.
                               try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                               exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                       +++ unfold SmallStepD.handle_jump in Hsn.
                           destruct (CFGProgD.get_block p (StackFrameD.fname sf_mid) bidf_mid) as [next_b_mid|] eqn:Hnb_mid.
                           *** unfold SmallStepD.handle_jump_aux in Hsn.
                               destruct (snd (BlockD.phi_function next_b_mid) (StackFrameD.curr_bid sf_mid)) eqn:Hphi_mid.
                               destruct (LocalsD.set_all (StackFrameD.locals sf_mid) (fst (BlockD.phi_function next_b_mid))
                                           (SmallStepD.eval_sexpr in_sexprs sf_mid)) as [locals_mid'|] eqn:Hset_mid.
                               ---- exfalso. simpl in Hsn.
                                    try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [_ [_ [_ [Hpc_eq _]]]].
                                    discriminate Hpc_eq.
                               ---- simpl in Hsn.
                                    try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                                    exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                           *** simpl in Hsn.
                               try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                               exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                   --- (* Jump: same reasoning, pc := 0 <> S pc2 *)
                       unfold SmallStepD.handle_jump in Hsn.
                       destruct (CFGProgD.get_block p (StackFrameD.fname sf_mid) jbid_mid) as [next_b_mid|] eqn:Hnb_mid.
                       +++ unfold SmallStepD.handle_jump_aux in Hsn.
                           destruct (snd (BlockD.phi_function next_b_mid) (StackFrameD.curr_bid sf_mid)) eqn:Hphi_mid.
                           destruct (LocalsD.set_all (StackFrameD.locals sf_mid) (fst (BlockD.phi_function next_b_mid))
                                       (SmallStepD.eval_sexpr in_sexprs sf_mid)) as [locals_mid'|] eqn:Hset_mid.
                           *** exfalso. simpl in Hsn.
                               try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [_ [_ [_ [Hpc_eq _]]]].
                               discriminate Hpc_eq.
                           *** simpl in Hsn.
                               try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                               exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                       +++ simpl in Hsn.
                           try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                           exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                   --- (* ReturnBlock: unlike [const_at_pc_assign], this is a
                       legitimate target scenario too (the resumed-into
                       frame's own instruction, at (fname2,bid2,pc2), can
                       be a call -- that's exactly what well-formedness
                       would tell us -- and [v2] simply isn't among its
                       outputs either). *)
                       unfold SmallStepD.handle_return in Hsn.
                       destruct rsf_mid as [| sf2 rsf2] eqn:Hrsfmid.
                       +++ simpl in Hsn.
                           try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                           exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                       +++ destruct (CFGProgD.get_block p (StackFrameD.fname sf2) (StackFrameD.curr_bid sf2)) as [bR|] eqn:HblockR.
                           *** destruct (List.nth_error (BlockD.instructions bR) (StackFrameD.pc sf2)) as [instrR|] eqn:HnthR.
                               ---- unfold SmallStepD.execute_assignment in Hsn.
                                    destruct (LocalsD.set_all (StackFrameD.locals sf2) (InstrD.output instrR)
                                                (SmallStepD.eval_sexpr ret_sexprs_mid sf_mid)) as [localsR'|] eqn:HsetR.
                                    ++++ (* success: target scenario -- the returned-into frame
                                         sf2 sits exactly at (fname2,bid2,pc2) *)
                                         simpl in Hsn.
                                         try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                                         simpl in Hfn_eq, Hloc_eq, Hbid_eq, Hpc_eq.
                                         assert (Hpc2_eq : StackFrameD.pc sf2 = pc2) by lia.
                                         assert (HbR_eq : bR = b2).
                                         { rewrite Hfn_eq, Hbid_eq in HblockR. rewrite Hblock2 in HblockR. injection HblockR as HblockR. exact (eq_sym HblockR). }
                                         subst bR.
                                         assert (HinstrR_eq : instrR = i2).
                                         { rewrite Hpc2_eq in HnthR. rewrite Hnth2 in HnthR. injection HnthR as HnthR. exact (eq_sym HnthR). }
                                         subst instrR.
                                         rewrite <- Hloc_eq.
                                         assert (HvalR : LocalsD.get localsR' v2 = LocalsD.get (StackFrameD.locals sf2) v2)
                                           by exact (set_all_not_in_preserves (InstrD.output i2) (SmallStepD.eval_sexpr ret_sexprs_mid sf_mid)
                                                       (StackFrameD.locals sf2) localsR' v2 Hnotin2 HsetR).
                                         rewrite HvalR.
                                         assert (Hsmid_shape : s_mid.(StateD.call_stack) = [sf_mid] ++ {| fname := fname2; locals := StackFrameD.locals sf2; curr_bid := bid2; pc := pc2 |} :: rsf2).
                                         { simpl. rewrite Hsmid.
                                           rewrite <- Hfn_eq, <- Hbid_eq, <- Hpc2_eq.
                                           destruct sf2; reflexivity. }
                                         assert (Hrest_eq : rsf2 = rest) by exact Hrsf_eq.
                                         subst rsf2.
                                         exact (IH n' Hlt p fname2 bid2 pc2 v2 c2 Hprev2
                                                  s0 s_mid f [sf_mid] rest locals0 (StackFrameD.locals sf2) Hgetf Hwf0 Hs0 Heval_mid Hsmid_shape).
                                    ++++ simpl in Hsn.
                                         try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                                         exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                               ---- simpl in Hsn.
                                    try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                                    exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                           *** simpl in Hsn.
                               try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                               exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                   --- (* Terminate: frame untouched, only status changes *)
                       unfold SmallStepD.handle_terminate in Hsn.
                       simpl in Hsn.
                       try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                       exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                ** simpl in Hsn.
                   try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                   exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
      + (* const_at_pc_assign *)
        destruct n as [| n'].
        * (* n = 0: sn = s0, but pc mismatch (0 vs S pc3) *)
          simpl in Heval. injection Heval as Heval. subst sn.
          rewrite Hs0 in Hsn.
          try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [_ [_ [_ [Hpc_eq _]]]].
          discriminate Hpc_eq.
        * (* n = S n' *)
          assert (Hlt : n' < S n') by lia.
          destruct (eval_split_last n' p s0 sn Heval) as [s_mid [Heval_mid Hstep_mid]].
          assert (Hwf_mid : call_stack_wf p s_mid.(StateD.call_stack))
            by exact (eval_preserves_call_stack_wf n' p s0 s_mid Hwf0 Heval_mid).
          destruct (s_mid.(StateD.call_stack)) as [| sf_mid rsf_mid] eqn:Hsmid.
          -- (* s_mid.call_stack = nil: impossible, mirrors the nil
             case in [step_preserves_buried_frame]. *)
             exfalso.
             unfold SmallStepD.step in Hstep_mid.
             destruct (StateD.status s_mid); try discriminate.
             unfold SmallStepD.get_next_instr in Hstep_mid.
             rewrite Hsmid in Hstep_mid.
             injection Hstep_mid as Hstep_mid.
             subst sn.
             unfold SmallStepD.handle_block_exit in Hsn.
             rewrite Hsmid in Hsn.
             unfold SmallStepD.error in Hsn.
             simpl in Hsn.
             rewrite Hsmid in Hsn.
             discriminate Hsn.
          -- (* the recurring pattern: if the last step left [sf_mid]
             untouched (any error branch, or [Terminate]), [s_mid] is
             *already* at our target, reached in fewer steps -- apply
             the induction hypothesis directly. Phrased over the four
             individual fields (matching what [frame_cons_eq_fields]
             gives) rather than one record equality, since assembling
             the record back would need its own (also fragile) case
             analysis. *)
             assert (Hih_unchanged :
                       StackFrameD.fname sf_mid = fname3 -> StackFrameD.locals sf_mid = locals_n ->
                       StackFrameD.curr_bid sf_mid = bid3 -> StackFrameD.pc sf_mid = S pc3 ->
                       rsf_mid = rest ->
                       LocalsD.get locals_n v3 = c3).
             { intros Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq.
               assert (Hsf_eq : sf_mid = {| fname := fname3; locals := locals_n; curr_bid := bid3; pc := S pc3 |}).
               { destruct sf_mid as [f0 l0 cb0 p0]. simpl in *. subst. reflexivity. }
               subst sf_mid rsf_mid.
               exact (IH n' Hlt p fname3 bid3 (S pc3) v3 c3
                        (const_at_pc_assign p fname3 bid3 pc3 b3 i3 v3 c3 k3 x3 Hblock3 Hnth3 Hop3 Hout3 Hin3 Hdisj3)
                        s0 s_mid f [] rest locals0 locals_n Hgetf Hwf0 Hs0 Heval_mid Hsmid). }
             unfold SmallStepD.step in Hstep_mid.
             destruct (StateD.status s_mid) eqn:Hstatus_mid; try discriminate.
             unfold SmallStepD.get_next_instr in Hstep_mid.
             rewrite Hsmid in Hstep_mid.
             destruct (CFGProgD.get_instr p (StackFrameD.fname sf_mid) (StackFrameD.curr_bid sf_mid) (StackFrameD.pc sf_mid))
               as [instr_mid|] eqn:Hinstr_mid.
             ++ (* execute_instr fired *)
                injection Hstep_mid as Hstep_mid.
                subst sn.
                unfold SmallStepD.execute_instr in Hsn.
                rewrite Hsmid in Hsn.
                destruct (InstrD.op instr_mid) as [[callee_mid | opcode_mid] | aux_mid] eqn:Hop_mid.
                ** (* function call *)
                   unfold SmallStepD.execute_func in Hsn.
                   destruct (CFGProgD.get_func p callee_mid) as [func_mid|] eqn:Hfunc_mid.
                   --- destruct (LocalsD.set_all LocalsD.empty (CFGFunD.args func_mid)
                                   (SmallStepD.eval_sexpr (InstrD.input instr_mid) sf_mid)) as [locals_mid'|] eqn:Hset_mid.
                       +++ (* success: push -- a fresh frame always has pc = 0, but our target has pc = S pc3 <> 0 *)
                           exfalso. simpl in Hsn.
                           try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [_ [_ [_ [Hpc_eq _]]]].
                           discriminate Hpc_eq.
                       +++ (* error: unchanged *)
                           simpl in Hsn.
                           try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                           exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                   --- (* error: unchanged *)
                       simpl in Hsn.
                       try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                       exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                ** (* opcode: ruled out, since the instruction at
                   (fname3,bid3,pc3) is specifically i3, an ASSIGN *)
                   unfold SmallStepD.execute_opcode in Hsn.
                   destruct (D.execute_opcode (StateD.dialect_state s_mid) opcode_mid
                               (SmallStepD.eval_sexpr (InstrD.input instr_mid) sf_mid))
                     as [[out_vals dialect_state'] status'].
                   unfold SmallStepD.execute_assignment in Hsn.
                   destruct (LocalsD.set_all (StackFrameD.locals sf_mid) (InstrD.output instr_mid) out_vals)
                     as [locals_mid'|] eqn:Hset_mid.
                   --- exfalso.
                       simpl in Hsn.
                       try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [_ [Hbid_eq [Hpc_eq _]]]].
                       simpl in Hfn_eq, Hbid_eq, Hpc_eq. assert (Hpc_eq' : StackFrameD.pc sf_mid = pc3) by lia.
                       assert (Hinstr_eq : CFGProgD.get_instr p fname3 bid3 pc3 = Some instr_mid).
                       { rewrite <- Hfn_eq, <- Hbid_eq, <- Hpc_eq'. exact Hinstr_mid. }
                       assert (Hget_i3 : CFGProgD.get_instr p fname3 bid3 pc3 = Some i3).
                       { unfold CFGProgD.get_instr. rewrite Hblock3. exact Hnth3. }
                       rewrite Hget_i3 in Hinstr_eq.
                       injection Hinstr_eq as Hinstr_eq.
                       subst instr_mid.
                       rewrite Hop3 in Hop_mid.
                       discriminate Hop_mid.
                   --- (* error: unchanged *)
                       simpl in Hsn.
                       try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                       exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                ** (* assign: the target scenario *)
                   destruct aux_mid.
                   unfold SmallStepD.execute_assignment in Hsn.
                   destruct (LocalsD.set_all (StackFrameD.locals sf_mid) (InstrD.output instr_mid)
                               (SmallStepD.eval_sexpr (InstrD.input instr_mid) sf_mid)) as [locals_mid'|] eqn:Hset_mid.
                   --- simpl in Hsn.
                       try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                       simpl in Hfn_eq, Hloc_eq, Hbid_eq, Hpc_eq. assert (Hpc_eq' : StackFrameD.pc sf_mid = pc3) by lia.
                       assert (Hinstr_eq : CFGProgD.get_instr p fname3 bid3 pc3 = Some instr_mid).
                       { rewrite <- Hfn_eq, <- Hbid_eq, <- Hpc_eq'. exact Hinstr_mid. }
                       assert (Hget_i3 : CFGProgD.get_instr p fname3 bid3 pc3 = Some i3).
                       { unfold CFGProgD.get_instr. rewrite Hblock3. exact Hnth3. }
                       rewrite Hget_i3 in Hinstr_eq.
                       injection Hinstr_eq as Hinstr_eq.
                       subst instr_mid.
                       assert (Hinput_val : nth_error (SmallStepD.eval_sexpr (InstrD.input i3) sf_mid) k3 =
                                             Some (match x3 with inl var => LocalsD.get sf_mid.(StackFrameD.locals) var | inr val => val end)).
                       { exact (eval_sexpr_nth_error (InstrD.input i3) sf_mid k3 x3 Hin3). }
                       assert (Hval3 : LocalsD.get locals_mid' v3 =
                                       match x3 with inl var => LocalsD.get sf_mid.(StackFrameD.locals) var | inr val => val end).
                       { exact (set_all_nth_error (InstrD.output i3) (SmallStepD.eval_sexpr (InstrD.input i3) sf_mid)
                                  (StackFrameD.locals sf_mid) locals_mid' k3 v3 _
                                  (i3.(InstrD.H_nodup)) Hset_mid Hout3 Hinput_val). }
                       rewrite <- Hloc_eq.
                       destruct Hdisj3 as [[v' [Hx3_eq Hprev]] | [val [Hx3_eq Hc3_eq]]].
                       +++ subst x3.
                           rewrite Hval3.
                           assert (Hsmid_shape : s_mid.(StateD.call_stack) = [] ++ {| fname := fname3; locals := StackFrameD.locals sf_mid; curr_bid := bid3; pc := pc3 |} :: rest).
                           { simpl. rewrite Hsmid, <- Hrsf_eq.
                             rewrite <- Hfn_eq, <- Hbid_eq, <- Hpc_eq'.
                             destruct sf_mid; reflexivity. }
                           exact (IH n' Hlt p fname3 bid3 pc3 v' c3 Hprev
                                    s0 s_mid f [] rest locals0 (StackFrameD.locals sf_mid) Hgetf Hwf0 Hs0 Heval_mid Hsmid_shape).
                       +++ subst x3. rewrite Hval3, Hc3_eq. reflexivity.
                   --- (* error: unchanged *)
                       simpl in Hsn.
                       try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                       exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
             ++ (* handle_block_exit fired *)
                injection Hstep_mid as Hstep_mid.
                subst sn.
                unfold SmallStepD.handle_block_exit in Hsn.
                rewrite Hsmid in Hsn.
                destruct (CFGProgD.get_block p (StackFrameD.fname sf_mid) (StackFrameD.curr_bid sf_mid)) as [b_mid|] eqn:Hblock_mid.
                ** destruct (BlockD.exit_info b_mid) as [cond_var_mid bidt_mid bidf_mid | jbid_mid | ret_sexprs_mid | ] eqn:Hexit_mid.
                   --- (* ConditionalJump: a successful jump always sets pc := 0, contradicting S pc3 <> 0 *)
                       unfold SmallStepD.handle_cond_jump in Hsn.
                       simpl in Hsn.
                       destruct (D.is_true_value (LocalsD.get (StackFrameD.locals sf_mid) cond_var_mid)) eqn:Hcond_mid.
                       +++ unfold SmallStepD.handle_jump in Hsn.
                           destruct (CFGProgD.get_block p (StackFrameD.fname sf_mid) bidt_mid) as [next_b_mid|] eqn:Hnb_mid.
                           *** unfold SmallStepD.handle_jump_aux in Hsn.
                               destruct (snd (BlockD.phi_function next_b_mid) (StackFrameD.curr_bid sf_mid)) eqn:Hphi_mid.
                               destruct (LocalsD.set_all (StackFrameD.locals sf_mid) (fst (BlockD.phi_function next_b_mid))
                                           (SmallStepD.eval_sexpr in_sexprs sf_mid)) as [locals_mid'|] eqn:Hset_mid.
                               ---- exfalso. simpl in Hsn.
                                    try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [_ [_ [_ [Hpc_eq _]]]].
                                    discriminate Hpc_eq.
                               ---- simpl in Hsn.
                                    try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                                    exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                           *** simpl in Hsn.
                               try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                               exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                       +++ unfold SmallStepD.handle_jump in Hsn.
                           destruct (CFGProgD.get_block p (StackFrameD.fname sf_mid) bidf_mid) as [next_b_mid|] eqn:Hnb_mid.
                           *** unfold SmallStepD.handle_jump_aux in Hsn.
                               destruct (snd (BlockD.phi_function next_b_mid) (StackFrameD.curr_bid sf_mid)) eqn:Hphi_mid.
                               destruct (LocalsD.set_all (StackFrameD.locals sf_mid) (fst (BlockD.phi_function next_b_mid))
                                           (SmallStepD.eval_sexpr in_sexprs sf_mid)) as [locals_mid'|] eqn:Hset_mid.
                               ---- exfalso. simpl in Hsn.
                                    try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [_ [_ [_ [Hpc_eq _]]]].
                                    discriminate Hpc_eq.
                               ---- simpl in Hsn.
                                    try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                                    exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                           *** simpl in Hsn.
                               try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                               exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                   --- (* Jump: same reasoning, pc := 0 contradicts S pc3 <> 0 *)
                       unfold SmallStepD.handle_jump in Hsn.
                       destruct (CFGProgD.get_block p (StackFrameD.fname sf_mid) jbid_mid) as [next_b_mid|] eqn:Hnb_mid.
                       +++ unfold SmallStepD.handle_jump_aux in Hsn.
                           destruct (snd (BlockD.phi_function next_b_mid) (StackFrameD.curr_bid sf_mid)) eqn:Hphi_mid.
                           destruct (LocalsD.set_all (StackFrameD.locals sf_mid) (fst (BlockD.phi_function next_b_mid))
                                       (SmallStepD.eval_sexpr in_sexprs sf_mid)) as [locals_mid'|] eqn:Hset_mid.
                           *** exfalso. simpl in Hsn.
                               try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [_ [_ [_ [Hpc_eq _]]]].
                               discriminate Hpc_eq.
                           *** simpl in Hsn.
                               try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                               exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                       +++ simpl in Hsn.
                           try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                           exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                   --- (* ReturnBlock: the case needing the well-formedness invariant *)
                       unfold SmallStepD.handle_return in Hsn.
                       destruct rsf_mid as [| sf2 rsf2] eqn:Hrsfmid.
                       +++ simpl in Hsn.
                           try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                           exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                       +++ destruct (CFGProgD.get_block p (StackFrameD.fname sf2) (StackFrameD.curr_bid sf2)) as [b2'|] eqn:Hblock2'.
                           *** destruct (List.nth_error (BlockD.instructions b2') (StackFrameD.pc sf2)) as [instr2'|] eqn:Hnth2'.
                               ---- unfold SmallStepD.execute_assignment in Hsn.
                                    destruct (LocalsD.set_all (StackFrameD.locals sf2) (InstrD.output instr2')
                                                (SmallStepD.eval_sexpr ret_sexprs_mid sf_mid)) as [locals2'|] eqn:Hset2.
                                    ++++ (* success: derive False from well-formedness *)
                                         exfalso.
                                         simpl in Hsn.
                                         try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [_ [Hbid_eq [Hpc_eq _]]]].
                                         simpl in Hfn_eq, Hbid_eq, Hpc_eq.
                                         assert (Hpc2_eq : StackFrameD.pc sf2 = pc3) by lia.
                                         simpl in Hwf_mid.
                                         destruct Hwf_mid as [Hfcall _].
                                         destruct Hfcall as [b' [instr' [callee' [Hb' [Hnth' Hop']]]]].
                                         rewrite Hfn_eq in Hb'. rewrite Hbid_eq in Hb'.
                                         rewrite Hblock3 in Hb'. injection Hb' as Hb'. subst b'.
                                         rewrite Hpc2_eq in Hnth'.
                                         rewrite Hnth3 in Hnth'. injection Hnth' as Hnth'. subst instr'.
                                         rewrite Hop3 in Hop'.
                                         discriminate Hop'.
                                    ++++ simpl in Hsn.
                                         try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                                         exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                               ---- simpl in Hsn.
                                    try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                                    exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                           *** simpl in Hsn.
                               try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                               exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                   --- (* Terminate: frame untouched, only status changes *)
                       unfold SmallStepD.handle_terminate in Hsn.
                       simpl in Hsn.
                       try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                       exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                ** (* block not found: error, unchanged *)
                   simpl in Hsn.
                   try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                   exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
      + (* const_at_pc_opcode: symmetric to [const_at_pc_assign], with
        the "assign" and "opcode" roles of ruled-out/target swapped, and
        with [const_sexprs_eval_gen] discharging the "all inputs
        constant" premise, plus [D.opcode_indep_state_snd] bridging the
        premise's [D.empty_dialect_state] against the actual run's
        current dialect state. *)
        destruct n as [| n'].
        * (* n = 0: sn = s0, but pc mismatch (0 vs S pc4) *)
          simpl in Heval. injection Heval as Heval. subst sn.
          rewrite Hs0 in Hsn.
          try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [_ [_ [_ [Hpc_eq _]]]].
          discriminate Hpc_eq.
        * (* n = S n' *)
          assert (Hlt : n' < S n') by lia.
          destruct (eval_split_last n' p s0 sn Heval) as [s_mid [Heval_mid Hstep_mid]].
          assert (Hwf_mid : call_stack_wf p s_mid.(StateD.call_stack))
            by exact (eval_preserves_call_stack_wf n' p s0 s_mid Hwf0 Heval_mid).
          destruct (s_mid.(StateD.call_stack)) as [| sf_mid rsf_mid] eqn:Hsmid.
          -- exfalso.
             unfold SmallStepD.step in Hstep_mid.
             destruct (StateD.status s_mid); try discriminate.
             unfold SmallStepD.get_next_instr in Hstep_mid.
             rewrite Hsmid in Hstep_mid.
             injection Hstep_mid as Hstep_mid.
             subst sn.
             unfold SmallStepD.handle_block_exit in Hsn.
             rewrite Hsmid in Hsn.
             unfold SmallStepD.error in Hsn.
             simpl in Hsn.
             rewrite Hsmid in Hsn.
             discriminate Hsn.
          -- assert (Hih_unchanged :
                       StackFrameD.fname sf_mid = fname4 -> StackFrameD.locals sf_mid = locals_n ->
                       StackFrameD.curr_bid sf_mid = bid4 -> StackFrameD.pc sf_mid = S pc4 ->
                       rsf_mid = rest ->
                       LocalsD.get locals_n v4 = c4).
             { intros Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq.
               assert (Hsf_eq : sf_mid = {| fname := fname4; locals := locals_n; curr_bid := bid4; pc := S pc4 |}).
               { destruct sf_mid as [f0 l0 cb0 p0]. simpl in *. subst. reflexivity. }
               subst sf_mid rsf_mid.
               exact (IH n' Hlt p fname4 bid4 (S pc4) v4 c4
                        (const_at_pc_opcode p fname4 bid4 pc4 b4 i4 opcode4 v4 c4 k4 ci4 rv4 st4
                           Hblock4 Hnth4 Hop4 Hindep4 Hsexprs4 Hexec4 Hout4 Hres4)
                        s0 s_mid f [] rest locals0 locals_n Hgetf Hwf0 Hs0 Heval_mid Hsmid). }
             unfold SmallStepD.step in Hstep_mid.
             destruct (StateD.status s_mid) eqn:Hstatus_mid; try discriminate.
             unfold SmallStepD.get_next_instr in Hstep_mid.
             rewrite Hsmid in Hstep_mid.
             destruct (CFGProgD.get_instr p (StackFrameD.fname sf_mid) (StackFrameD.curr_bid sf_mid) (StackFrameD.pc sf_mid))
               as [instr_mid|] eqn:Hinstr_mid.
             ++ (* execute_instr fired *)
                injection Hstep_mid as Hstep_mid.
                subst sn.
                unfold SmallStepD.execute_instr in Hsn.
                rewrite Hsmid in Hsn.
                destruct (InstrD.op instr_mid) as [[callee_mid | opcode_mid] | aux_mid] eqn:Hop_mid.
                ** (* function call: a successful push always has pc = 0 <> S pc4 *)
                   unfold SmallStepD.execute_func in Hsn.
                   destruct (CFGProgD.get_func p callee_mid) as [func_mid|] eqn:Hfunc_mid.
                   --- destruct (LocalsD.set_all LocalsD.empty (CFGFunD.args func_mid)
                                   (SmallStepD.eval_sexpr (InstrD.input instr_mid) sf_mid)) as [locals_mid'|] eqn:Hset_mid.
                       +++ exfalso. simpl in Hsn.
                           try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [_ [_ [_ [Hpc_eq _]]]].
                           discriminate Hpc_eq.
                       +++ simpl in Hsn.
                           try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                           exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                   --- simpl in Hsn.
                       try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                       exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                ** (* opcode: the target scenario *)
                   unfold SmallStepD.execute_opcode in Hsn.
                   destruct (D.execute_opcode (StateD.dialect_state s_mid) opcode_mid
                               (SmallStepD.eval_sexpr (InstrD.input instr_mid) sf_mid))
                     as [[out_vals dialect_state'] status'] eqn:Hexec_mid.
                   unfold SmallStepD.execute_assignment in Hsn.
                   destruct (LocalsD.set_all (StackFrameD.locals sf_mid) (InstrD.output instr_mid) out_vals)
                     as [locals_mid'|] eqn:Hset_mid.
                   --- simpl in Hsn.
                       try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                       simpl in Hfn_eq, Hloc_eq, Hbid_eq, Hpc_eq. assert (Hpc_eq' : StackFrameD.pc sf_mid = pc4) by lia.
                       assert (Hinstr_eq : CFGProgD.get_instr p fname4 bid4 pc4 = Some instr_mid).
                       { rewrite <- Hfn_eq, <- Hbid_eq, <- Hpc_eq'. exact Hinstr_mid. }
                       assert (Hget_i4 : CFGProgD.get_instr p fname4 bid4 pc4 = Some i4).
                       { unfold CFGProgD.get_instr. rewrite Hblock4. exact Hnth4. }
                       rewrite Hget_i4 in Hinstr_eq.
                       injection Hinstr_eq as Hinstr_eq.
                       subst instr_mid.
                       rewrite Hop4 in Hop_mid.
                       injection Hop_mid as Hop_mid.
                       subst opcode_mid.
                       assert (Hsmid_shape : s_mid.(StateD.call_stack) = [] ++ {| fname := fname4; locals := StackFrameD.locals sf_mid; curr_bid := bid4; pc := pc4 |} :: rest).
                       { simpl. rewrite Hsmid, <- Hrsf_eq.
                         rewrite <- Hfn_eq, <- Hbid_eq, <- Hpc_eq'.
                         destruct sf_mid; reflexivity. }
                       assert (Hval4 : forall (vv: VarID.t) (cc: D.value_t),
                                 const_at_pc p fname4 bid4 pc4 vv cc -> LocalsD.get (StackFrameD.locals sf_mid) vv = cc).
                       { intros vv cc Hvc.
                         exact (IH n' Hlt p fname4 bid4 pc4 vv cc Hvc
                                  s0 s_mid f [] rest locals0 (StackFrameD.locals sf_mid) Hgetf Hwf0 Hs0 Heval_mid Hsmid_shape). }
                       assert (Heval_ci4 : SmallStepD.eval_sexpr (InstrD.input i4) sf_mid = ci4)
                         by exact (const_sexprs_eval_gen (InstrD.input i4) p fname4 bid4 pc4 ci4 sf_mid Hsexprs4 Hval4).
                       rewrite Heval_ci4 in Hexec_mid.
                       destruct (D.opcode_indep_state_snd opcode4 Hindep4 (StateD.dialect_state s_mid) D.empty_dialect_state ci4)
                         as [res [status [Hexec_smid_indep Hexec_empty_indep]]].
                       rewrite Hexec4 in Hexec_empty_indep.
                       injection Hexec_empty_indep as Hres_eq Hst_eq Hstatus_eq.
                       subst res status.
                       rewrite Hexec_smid_indep in Hexec_mid.
                       injection Hexec_mid as Hout_eq Hdstate_eq Hstat_eq.
                       subst out_vals.
                       rewrite <- Hloc_eq.
                       exact (set_all_nth_error (InstrD.output i4) rv4 (StackFrameD.locals sf_mid) locals_mid' k4 v4 c4
                                (i4.(InstrD.H_nodup)) Hset_mid Hout4 Hres4).
                   --- simpl in Hsn.
                       try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                       exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                ** (* assign: ruled out, since the instruction at
                   (fname4,bid4,pc4) is specifically i4, an opcode *)
                   destruct aux_mid.
                   unfold SmallStepD.execute_assignment in Hsn.
                   destruct (LocalsD.set_all (StackFrameD.locals sf_mid) (InstrD.output instr_mid)
                               (SmallStepD.eval_sexpr (InstrD.input instr_mid) sf_mid)) as [locals_mid'|] eqn:Hset_mid.
                   --- exfalso.
                       simpl in Hsn.
                       try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [_ [Hbid_eq [Hpc_eq _]]]].
                       simpl in Hfn_eq, Hbid_eq, Hpc_eq. assert (Hpc_eq' : StackFrameD.pc sf_mid = pc4) by lia.
                       assert (Hinstr_eq : CFGProgD.get_instr p fname4 bid4 pc4 = Some instr_mid).
                       { rewrite <- Hfn_eq, <- Hbid_eq, <- Hpc_eq'. exact Hinstr_mid. }
                       assert (Hget_i4 : CFGProgD.get_instr p fname4 bid4 pc4 = Some i4).
                       { unfold CFGProgD.get_instr. rewrite Hblock4. exact Hnth4. }
                       rewrite Hget_i4 in Hinstr_eq.
                       injection Hinstr_eq as Hinstr_eq.
                       subst instr_mid.
                       rewrite Hop4 in Hop_mid.
                       discriminate Hop_mid.
                   --- simpl in Hsn.
                       try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                       exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
             ++ (* handle_block_exit fired *)
                injection Hstep_mid as Hstep_mid.
                subst sn.
                unfold SmallStepD.handle_block_exit in Hsn.
                rewrite Hsmid in Hsn.
                destruct (CFGProgD.get_block p (StackFrameD.fname sf_mid) (StackFrameD.curr_bid sf_mid)) as [b_mid|] eqn:Hblock_mid.
                ** destruct (BlockD.exit_info b_mid) as [cond_var_mid bidt_mid bidf_mid | jbid_mid | ret_sexprs_mid | ] eqn:Hexit_mid.
                   --- (* ConditionalJump: a successful jump always sets pc := 0, contradicting S pc4 <> 0 *)
                       unfold SmallStepD.handle_cond_jump in Hsn.
                       simpl in Hsn.
                       destruct (D.is_true_value (LocalsD.get (StackFrameD.locals sf_mid) cond_var_mid)) eqn:Hcond_mid.
                       +++ unfold SmallStepD.handle_jump in Hsn.
                           destruct (CFGProgD.get_block p (StackFrameD.fname sf_mid) bidt_mid) as [next_b_mid|] eqn:Hnb_mid.
                           *** unfold SmallStepD.handle_jump_aux in Hsn.
                               destruct (snd (BlockD.phi_function next_b_mid) (StackFrameD.curr_bid sf_mid)) eqn:Hphi_mid.
                               destruct (LocalsD.set_all (StackFrameD.locals sf_mid) (fst (BlockD.phi_function next_b_mid))
                                           (SmallStepD.eval_sexpr in_sexprs sf_mid)) as [locals_mid'|] eqn:Hset_mid.
                               ---- exfalso. simpl in Hsn.
                                    try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [_ [_ [_ [Hpc_eq _]]]].
                                    discriminate Hpc_eq.
                               ---- simpl in Hsn.
                                    try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                                    exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                           *** simpl in Hsn.
                               try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                               exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                       +++ unfold SmallStepD.handle_jump in Hsn.
                           destruct (CFGProgD.get_block p (StackFrameD.fname sf_mid) bidf_mid) as [next_b_mid|] eqn:Hnb_mid.
                           *** unfold SmallStepD.handle_jump_aux in Hsn.
                               destruct (snd (BlockD.phi_function next_b_mid) (StackFrameD.curr_bid sf_mid)) eqn:Hphi_mid.
                               destruct (LocalsD.set_all (StackFrameD.locals sf_mid) (fst (BlockD.phi_function next_b_mid))
                                           (SmallStepD.eval_sexpr in_sexprs sf_mid)) as [locals_mid'|] eqn:Hset_mid.
                               ---- exfalso. simpl in Hsn.
                                    try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [_ [_ [_ [Hpc_eq _]]]].
                                    discriminate Hpc_eq.
                               ---- simpl in Hsn.
                                    try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                                    exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                           *** simpl in Hsn.
                               try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                               exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                   --- (* Jump: same reasoning, pc := 0 contradicts S pc4 <> 0 *)
                       unfold SmallStepD.handle_jump in Hsn.
                       destruct (CFGProgD.get_block p (StackFrameD.fname sf_mid) jbid_mid) as [next_b_mid|] eqn:Hnb_mid.
                       +++ unfold SmallStepD.handle_jump_aux in Hsn.
                           destruct (snd (BlockD.phi_function next_b_mid) (StackFrameD.curr_bid sf_mid)) eqn:Hphi_mid.
                           destruct (LocalsD.set_all (StackFrameD.locals sf_mid) (fst (BlockD.phi_function next_b_mid))
                                       (SmallStepD.eval_sexpr in_sexprs sf_mid)) as [locals_mid'|] eqn:Hset_mid.
                           *** exfalso. simpl in Hsn.
                               try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [_ [_ [_ [Hpc_eq _]]]].
                               discriminate Hpc_eq.
                           *** simpl in Hsn.
                               try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                               exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                       +++ simpl in Hsn.
                           try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                           exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                   --- (* ReturnBlock: the case needing the well-formedness invariant *)
                       unfold SmallStepD.handle_return in Hsn.
                       destruct rsf_mid as [| sf2 rsf2] eqn:Hrsfmid.
                       +++ simpl in Hsn.
                           try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                           exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                       +++ destruct (CFGProgD.get_block p (StackFrameD.fname sf2) (StackFrameD.curr_bid sf2)) as [b2'|] eqn:Hblock2'.
                           *** destruct (List.nth_error (BlockD.instructions b2') (StackFrameD.pc sf2)) as [instr2'|] eqn:Hnth2'.
                               ---- unfold SmallStepD.execute_assignment in Hsn.
                                    destruct (LocalsD.set_all (StackFrameD.locals sf2) (InstrD.output instr2')
                                                (SmallStepD.eval_sexpr ret_sexprs_mid sf_mid)) as [locals2'|] eqn:Hset2.
                                    ++++ (* success: derive False from well-formedness *)
                                         exfalso.
                                         simpl in Hsn.
                                         try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [_ [Hbid_eq [Hpc_eq _]]]].
                                         simpl in Hfn_eq, Hbid_eq, Hpc_eq.
                                         assert (Hpc2_eq : StackFrameD.pc sf2 = pc4) by lia.
                                         simpl in Hwf_mid.
                                         destruct Hwf_mid as [Hfcall _].
                                         destruct Hfcall as [b' [instr' [callee' [Hb' [Hnth' Hop']]]]].
                                         rewrite Hfn_eq in Hb'. rewrite Hbid_eq in Hb'.
                                         rewrite Hblock4 in Hb'. injection Hb' as Hb'. subst b'.
                                         rewrite Hpc2_eq in Hnth'.
                                         rewrite Hnth4 in Hnth'. injection Hnth' as Hnth'. subst instr'.
                                         rewrite Hop4 in Hop'.
                                         discriminate Hop'.
                                    ++++ simpl in Hsn.
                                         try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                                         exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                               ---- simpl in Hsn.
                                    try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                                    exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                           *** simpl in Hsn.
                               try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                               exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                   --- (* Terminate: frame untouched, only status changes *)
                       unfold SmallStepD.handle_terminate in Hsn.
                       simpl in Hsn.
                       try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                       exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
                ** (* block not found: error, unchanged *)
                   simpl in Hsn.
                   try rewrite Hsmid in Hsn; destruct (frame_cons_eq_fields _ _ _ _ Hsn) as [Hfn_eq [Hloc_eq [Hbid_eq [Hpc_eq Hrsf_eq]]]].
                   exact (Hih_unchanged Hfn_eq Hloc_eq Hbid_eq Hpc_eq Hrsf_eq).
    - (* hl = a :: hl' : our frame is buried under a non-empty prefix.
      [n] cannot be 0 (s0 has a single frame on [rest]), so peel the
      last step and, by [step_preserves_buried_frame], recurse on
      [n' < n] with the *same* fact -- our frame is untouched by
      whatever that last step did. *)
      destruct n as [| n'].
      + simpl in Heval.
        injection Heval as Heval.
        subst sn.
        rewrite Hs0 in Hsn.
        exfalso.
        apply (f_equal (@List.length StackFrameD.t)) in Hsn.
        simpl in Hsn.
        rewrite List.length_app in Hsn.
        simpl in Hsn.
        lia.
      + destruct (eval_split_last n' p s0 sn Heval) as [s_mid [Heval_mid Hstep_mid]].
        destruct (step_preserves_buried_frame p s_mid sn a hl' rest
                    {| fname := fn; locals := locals_n; curr_bid := bid; pc := at_pc |}
                    Hsn Hstep_mid) as [hl'' Hmid_shape].
        assert (Hlt : n' < S n') by lia.
        exact (IH n' Hlt p fn bid at_pc v c Hconst s0 s_mid f hl'' rest locals0 locals_n Hgetf Hwf0 Hs0 Heval_mid Hmid_shape).
  Qed.

  (* If [v] is constant [c] at program point (fn, bid, at_pc) according
  to [const_at_pc], then starting from a state where [fn] was just
  called (a single fresh frame, at its own entry, on top of whichever
  [rest] of the call stack happens to be below -- we don't care who
  called it, or with what arguments), any execution that reaches
  (bid, at_pc) in that *same* call to [fn] (i.e., [rest] is still
  exactly the same underneath -- [fn] may have made and returned from
  any number of further calls of its own along the way, but must not
  itself have returned to its own caller) finds [v]'s actual value
  there to be exactly [c].

  (Note: the function name and program-point counter are called [fn]/
  [at_pc] here rather than [fname]/[pc], the names used everywhere
  else in this file -- those would otherwise shadow the [StackFrameD]
  field projections of the same names, breaking record field access
  below.) *)
  Theorem const_at_pc_snd :
    forall (p: CFGProgD.t) (fn: FuncName.t) (bid: BlockID.t) (at_pc: nat) (v: VarID.t) (c: D.value_t),
      const_at_pc p fn bid at_pc v c ->
      forall (n: nat) (s0 sn: StateD.t) (f: CFGFunD.t) (locals0 locals_n: LocalsD.t) (rest: CallStackD.t),
        CFGProgD.get_func p fn = Some f ->
        call_stack_wf p s0.(StateD.call_stack) ->
        s0.(StateD.call_stack) = {| fname := fn; locals := locals0; curr_bid := f.(entry_bid); pc := 0 |} :: rest ->
        SmallStepD.eval n s0 p = Some sn ->
        sn.(StateD.call_stack) = {| fname := fn; locals := locals_n; curr_bid := bid; pc := at_pc |} :: rest ->
        LocalsD.get locals_n v = c.
  Proof.
    intros p fn bid at_pc v c Hconst n s0 sn f locals0 locals_n rest Hgetf Hwf0 Hs0 Heval Hsn.
    exact (const_at_pc_snd_gen n p fn bid at_pc v c Hconst s0 sn f [] rest locals0 locals_n
             Hgetf Hwf0 Hs0 Heval Hsn).
  Qed.

End Constancy_snd.
