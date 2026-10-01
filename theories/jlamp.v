Require Import FORYU.state.
Require Import FORYU.program.
Require Import FORYU.semantics.
Require Import FORYU.liveness.
Require Import FORYU.liveness_snd.
Require Import FORYU.constancy_info.
Require Import FORYU.constancy.
Require Import FORYU.constancy_snd.
Require Import FORYU.constancy_checker_snd.
Require Import stdpp.prelude.
Require Import Lia.

(*

  This module includes a simplified version of the main statements
  that appear in liveness.v and liveness_snd.v (Section 4), and in 
  constancy.v, constancy_snd.v and constancy_checker_snd.v (Section 5).

*)

Module JLAMP (D: DIALECT).

  (* ** Liveness (Section 4) ** *)
  Module Liveness_JLAMP.

    Module Liveness_sndD := Liveness_snd(D).
    Module LivenessD := Liveness_sndD.LivenessD.
    Module SmallStepD := LivenessD.SmallStepD.
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
    Module DialectFactsD := Liveness_sndD.DialectFactsD.

    Import LivenessD.
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

    Import Liveness_sndD.


    (* Converts a list of simple expressions to a set of variables *)
    Definition list_sexp_to_varset (l : list SimpleExprD.t) :=
      (list_to_set (extract_yul_vars l)).

    (* States that two stack frames are at the same program point *)
    Definition same_pp (fname: FuncName.t) (bid: BlockID.t) (pc: nat) (sf1 sf2: StackFrameD.t) :=
      sf1.(StackFrameD.fname) = fname /\
        sf2.(StackFrameD.fname) = fname /\
        sf1.(StackFrameD.curr_bid) = bid /\
        sf2.(StackFrameD.curr_bid) = bid /\
        sf1.(StackFrameD.pc) = pc /\
        sf2.(StackFrameD.pc) = pc.

    (* States that two stack frames are equivalent up to the value of
    valriable v *)
    Definition equiv_frames_up_to_v (fname: FuncName.t) (bid: BlockID.t) (pc: nat) (v: VarID.t) (sf1 sf2: StackFrameD.t) :=
      same_pp fname bid pc sf1 sf2 /\
        forall v',
          v' <> v -> (* equality is required for variable different from v *)
          LocalsD.get sf1.(StackFrameD.locals) v'= LocalsD.get sf2.(StackFrameD.locals) v'.

    (* States that two program states are equivalent up to the value of
    valriable v in the top stack frame *)  
    Definition equiv_states_up_to_v (fname: FuncName.t) (bid: BlockID.t) (pc: nat) (v: VarID.t) (st1 st2: StateD.t) :=
      Nat.lt 0 (length (StateD.call_stack st1)) /\
      length (StateD.call_stack st1) = length (StateD.call_stack st2) /\
        st1.(StateD.status) = st2.(StateD.status) /\
        st1.(StateD.dialect_state) = st2.(StateD.dialect_state) /\ 
        exists sf1 sf2 rsf,
          st1.(StateD.call_stack) = sf1::rsf /\
            st2.(StateD.call_stack) = sf2::rsf /\
            equiv_frames_up_to_v fname bid pc v sf1 sf2.

    (* States that s is the set of variables that are immediately
    accessed in a block b wrt. to the rpogram counter pc *)
    Definition accessed_vars (b: BlockD.t) (pc: nat) (s: VarSet.t) :=
      ( pc = (length b.(BlockD.instructions)) /\ (* end of block *)
          match b.(BlockD.exit_info) with
          | ExitInfoD.ConditionalJump cv _ _ =>
              VarSet.Equal s (VarSet.add cv VarSet.empty) (* cv is accessed *)
          | ExitInfoD.ReturnBlock rvs =>
              VarSet.Equal s (list_sexp_to_varset rvs) (* rs are accessed *)
          | _ => VarSet.Equal s VarSet.empty (* nothing is accessed *)
          end )
      \/
        ( pc < (length b.(BlockD.instructions)) /\  (* within the block *)
            exists instr,                  
              nth_error b.(BlockD.instructions) pc = Some instr /\
                (VarSet.Equal s (list_sexp_to_varset instr.(InstrD.input)) )). (* instr.input are accessed *)

    (* States that top stack frames of states st1 and st2 are equivalent
    wrt. to the accessed variables *)  
    Definition equiv_top_frame (p: CFGProgD.t) (st1 st2: StateD.t) :=
      match st1.(StateD.call_stack), st2.(StateD.call_stack) with
      | nil,nil => True (* both call stacks are empty *)
      | sf1::_,sf2::_ => (* top frames agree on values of accessed variables *)
          same_pp sf1.(StackFrameD.fname) sf1.(StackFrameD.curr_bid) sf1.(StackFrameD.pc) sf1 sf2 /\
            forall v s b,
              CFGProgD.get_block p sf1.(StackFrameD.fname) sf1.(StackFrameD.curr_bid) = Some b ->
              Liveness_sndD.accessed_vars b sf1.(StackFrameD.pc) s ->
              VarSet.In v s ->
              LocalsD.get sf1.(StackFrameD.locals) v = LocalsD.get sf2.(StackFrameD.locals) v (* we use = here for simplicity, the more general uses D.eqb *)
      | _,_ => False (* one of the call stacks is empty *)
      end.

    (* Defines when a variable v is considered dead: changing its value
    (st1 and st2 differ only in v) is not observable -- after any number
    of steps, both executions are at the same program point, with the
    same status and dialect state, and agree on the values of the
    variables accessed there *)
    Definition dead_variable (p: CFGProgD.t) (fname: FuncName.t) (bid: BlockID.t) (pc: nat) (v: VarID.t) :=
      forall (st1 st2 st1': StateD.t) (n: nat),
        equiv_states_up_to_v fname bid pc v st1 st2 ->
        SmallStepD.eval n st1 p = Some st1' ->
        exists st2',
          SmallStepD.eval n st2 p = Some st2' /\
            st1'.(StateD.status) = st2'.(StateD.status) /\ (* same status *)
            st1'.(StateD.dialect_state) = st2'.(StateD.dialect_state) /\ (* same dialect state *)
            equiv_top_frame p st1' st2'.

    (* This lemma relates the equivalence of states defined in this
    module to that defined in liveness_snd.v *)
    Lemma equiv_state_rel:
      forall p fname bid pc v st1 st2,
        equiv_states_up_to_v fname bid pc v st1 st2 ->
        equiv_states_up_to_i_v p (length st1.(StateD.call_stack) -1) fname bid pc v st1 st2.
    Proof.
      intros p fname bid pc v st1 st2 H_equiv_st1_st2.
      unfold equiv_states_up_to_i_v.
      unfold equiv_states_up_to_v in H_equiv_st1_st2.
      destruct H_equiv_st1_st2 as [H_not_empty [H_len_call_stack [H_status [H_dialect [sf1 [sf2 [rsf [H_call_stack_st1 [H_call_stack_st2 H_equiv_frames]]]]]]]]].

      unfold equiv_frames_up_to_v in H_equiv_frames.
      unfold same_pp in H_equiv_frames.
      destruct H_equiv_frames as [ [H_fname_sf1 [H_fname_sf2 [H_bid_sf1 [H_bid_sf2 [H_pc_sf1 H_pc_sf2 ]]]]] H_equiv_varmap].

      repeat split; try assumption.
      - lia.
      - exists [].
        exists rsf.
        exists sf1.
        exists sf2.

        repeat split; try (assumption || lia).       
        + rewrite H_call_stack_st1. simpl. lia.
        + rewrite H_call_stack_st1. simpl. lia.
        + unfold equiv_locals_up_to_v.
          intros v' H_neq_v'_v.
          rewrite DialectFactsD.eqb_eq.
          apply (H_equiv_varmap v' H_neq_v'_v).
    Qed.

    (* This function is the liveness checker, it simply uses the one
    defined in liveness.v --- just to use the same name that is used in
    the paper *)
    Definition liveness_chk (p: CFGProgD.t) (r: prog_live_info_t) :=
      check_program p r.

    (* Just an aliasing of Liveness_sndD.snd_all_blocks_info -- just to
    use the same name that is used in the paper. It states that the
    liveness information [r] is a solution of the liveness equations,
    taken as a whole: the in/out sets of every block are related to
    each other, and to those of its successors, as the equations
    require. *)
    Definition liveness_info_snd := Liveness_sndD.snd_all_blocks_info.

    (* This lemma states that sound liveness information provides a
    sound under-approximation of dead variables: a variable that is not
    in the in-set of a block is dead at the entry of the block. The
    proof uses the corresponding (more general) lemmas that appear in
    liveness_snd.v *)
    Lemma liveness_info_snd_dead:
      forall (p: CFGProgD.t) (r: prog_live_info_t) fname bid b f_info b_in_info b_out_info,
        liveness_info_snd p r ->
        CFGProgD.get_block p fname bid = Some b ->
        r fname = Some f_info ->
        f_info bid = Some (b_in_info, b_out_info) ->
        forall v, ~ VarSet.In v b_in_info -> dead_variable p fname bid 0 v.
    Proof.
      unfold dead_variable.
      intros p r fname bid b f_info b_in_info b_out_info H_snd H_b_exists H_r_f H_f_info
             v H_not_In_v_s st1 st2 st1' n H_st1_equiv_st2 H_eval.

      (* the in-set that r assigns to the block satisfies live_in *)
      pose proof (snd_info p r H_snd fname bid b H_b_exists)
        as [f_info' [b_in_info' [b_out_info' [H_r_f' [H_f_info' [H_live_in _]]]]]].
      rewrite H_r_f in H_r_f'. injection H_r_f' as H_r_f'. subst f_info'.
      rewrite H_f_info in H_f_info'. injection H_f_info' as H_in_eq _. subst b_in_info'.

      apply (live_at_pc_zero_eq_live_in p fname bid b b_in_info H_b_exists) in H_live_in.

      pose proof (equiv_state_rel p fname bid 0%nat v st1 st2 H_st1_equiv_st2) as H_st1_equiv_st2_gen.

      remember (length st1.(StateD.call_stack)) as i eqn:E_i. 

      pose proof (live_at_snd p n fname bid b 0%nat b_in_info H_b_exists H_live_in st1 st2 st1' v (i-1) H_st1_equiv_st2_gen H_eval H_not_In_v_s) as [st2' [bid' [b' [pc' [s' [H_eval_st2 [H_b'_exists [H_equiv_st1'_st2'_gen H_equiv_top_frame_gen]]]]]]]].

      (* both kinds of states returned by live_at_snd have the same
      status and dialect state *)
      assert (H_status_dialect :
                st1'.(StateD.status) = st2'.(StateD.status) /\
                st1'.(StateD.dialect_state) = st2'.(StateD.dialect_state)).
      { destruct H_equiv_st1'_st2'_gen as [[H_equiv_gen _] | H_eq].
        - destruct H_equiv_gen as [_ [_ [H_status [H_dialect _]]]].
          split; assumption.
        - subst st2'. split; reflexivity. }
      destruct H_status_dialect as [H_status H_dialect].

      exists st2'.
      split; [ | split; [ | split]].
      - apply H_eval_st2.
      - apply H_status.
      - apply H_dialect.
      - unfold equiv_vars_in_top_frame in H_equiv_top_frame_gen.
        unfold equiv_top_frame.
        destruct (StateD.call_stack st1') as [|sf1' rs1']; try assumption.
        destruct (StateD.call_stack st2') as [|sf2' rs2']; try assumption.
        destruct H_equiv_top_frame_gen as [H_fname_sf1'_sf2' [H_bid_sf1'_sf2' [H_pc_sf1'_sf2' H_equiv_varmap]]].
        split.
        + unfold same_pp.       
          repeat split; try (assumption || intuition).
        + intros v0 s0 b0 H_get_block H_acc H_In_v0_s0.
          rewrite <- DialectFactsD.eqb_eq.
          apply (H_equiv_varmap v0 s0 b0 H_get_block H_acc H_In_v0_s0).
    Qed.

    (* This proves the soundness and completeness of the checker -- it
    uses the corresponding lemma that appears in liveness_snd.v *)
    Lemma liveness_chk_snd_cmp: 
      forall (p: CFGProgD.t) (r: prog_live_info_t),
        CFGProgD.valid_program p ->
        (liveness_info_snd p r <-> liveness_chk p r = true).
    Proof.
      apply check_valid_prog_correct.
    Qed.

  End Liveness_JLAMP.

  (* ** Constancy (Section 5) ** *)
  Module Constancy_JLAMP.

    Module ConstChkD := Constancy_checker_snd(D).
    Module ConstD := ConstChkD.ConstD.
    Module ConstSndD := ConstChkD.ConstSndD.
    Module CFGProgD := ConstD.CFGProgD.
    Module StateD := ConstD.StateD.
    Module CallStackD := ConstD.CallStackD.
    Module StackFrameD := ConstD.StackFrameD.
    Module LocalsD := ConstD.LocalsD.
    Module CFGFunD := ConstD.CFGFunD.
    Module BlockD := ConstD.BlockD.
    Module InstrD := ConstD.InstrD.
    Module SimpleExprD := ConstD.SimpleExprD.

    (* The types of the constancy information: one map from variables
    to values per program point of each block (see constancy_info.v) *)
    Definition pp_const_info_t := ConstD.pp_const_info_t.
    Definition block_const_info_t := ConstD.block_const_info_t.
    Definition func_const_info_t := ConstD.func_const_info_t.
    Definition prog_const_info_t := ConstD.prog_const_info_t.

    (* [constant_var p fn bid pc v c]: whenever an execution of a call
    to [fn] reaches the program point (fn,bid,pc), with the same frames
    [rest] below the frame of [fn], the value of [v] is [c]. This is
    the definition of constancy_snd.v, where the program counter is
    called [at_pc] *)
    Definition constant_var (p: CFGProgD.t) (fn: FuncName.t) (bid: BlockID.t) (pc: nat) (v: VarID.t) (c: D.value_t) : Prop :=
      forall (n: nat) (s0 sn: StateD.t) (f: CFGFunD.t) (locals0 locals_n: LocalsD.t) (rest: CallStackD.t),
        CFGProgD.get_func p fn = Some f ->
        s0.(StateD.call_stack) =
          {| StackFrameD.fname := fn; StackFrameD.locals := locals0;
             StackFrameD.curr_bid := f.(CFGFunD.entry_bid); StackFrameD.pc := 0 |} :: rest ->
        ConstD.SmallStepD.eval n s0 p = Some sn ->
        sn.(StateD.call_stack) =
          {| StackFrameD.fname := fn; StackFrameD.locals := locals_n;
             StackFrameD.curr_bid := bid; StackFrameD.pc := pc |} :: rest ->
        LocalsD.get locals_n v = c.

    (* The conditions on the constancy information (see
    constancy_snd.v and constancy_checker_snd.v) *)
    Definition sexpr_const := ConstSndD.sexpr_const.
    Definition const_phi := ConstSndD.const_phi.
    Definition instr_snd := ConstChkD.instr_snd.
    Definition edge_info_snd := ConstChkD.edge_info_snd.
    Definition block_info_snd := ConstChkD.block_info_snd.

    (* [const_info_snd p r]: the constancy information [r] is valid
    for [p], taken as a whole *)
    Definition const_info_snd := ConstChkD.const_info_snd.

    (* The constancy checker: it simply uses [check_const_program],
    defined in constancy.v --- just to use the same name that is used
    in the paper *)
    Definition constancy_chk (p: CFGProgD.t) (r: prog_const_info_t) :=
      ConstD.check_const_program p r.

    (* Valid constancy information is sound: every fact it claims at a
    program point holds there *)
    Lemma const_info_snd_constant_var:
      forall (p: CFGProgD.t) (r: prog_const_info_t) fn f f_info bid b b_info pc m v c,
        const_info_snd p r ->
        CFGProgD.get_func p fn = Some f ->
        r fn = Some f_info ->
        CFGProgD.get_block p fn bid = Some b ->
        f_info bid = Some b_info ->
        nth_error b_info pc = Some m -> (* m is the map at pc *)
        VarMap.find v m = Some c -> (* m claims that v is c *)
        constant_var p fn bid pc v c.
    Proof.
      intros p r fn f f_info bid b b_info pc m v c H_snd.
      exact (ConstChkD.const_info_snd_constant_var p r H_snd fn f f_info bid b b_info pc m v c).
    Qed.

    (* Soundness and completeness of the checker *)
    Lemma const_chk_snd_cmp:
      forall (p: CFGProgD.t) (r: prog_const_info_t),
        CFGProgD.valid_program p ->
        (const_info_snd p r <-> constancy_chk p r = true).
    Proof.
      exact ConstChkD.const_chk_snd_cmp.
    Qed.

  End Constancy_JLAMP.

End JLAMP.
