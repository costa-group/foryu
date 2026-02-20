Require Import FORYU.state.
Require Import FORYU.program.
Require Import FORYU.semantics.
Require Import FORYU.liveness.
Require Import FORYU.liveness_snd.
Require Import stdpp.prelude.
Require Import Lia.

(*

  This module includes a simplified version of the main statements
  that appear in liveness.v and liveness_snd.v, which is used in
  Section 4 of the FM26 submission.

*)

Module FM26 (D: DIALECT).

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
        let fname := sf1.(StackFrameD.fname) in
        let bid := sf1.(StackFrameD.curr_bid) in
        let pc := sf1.(StackFrameD.pc) in
        same_pp fname bid pc sf1 sf2 /\
          forall v s b,
            CFGProgD.get_block p fname bid = Some b ->
            Liveness_sndD.accessed_vars b pc s ->
            VarSet.In v s ->
            LocalsD.get sf1.(StackFrameD.locals) v = LocalsD.get sf2.(StackFrameD.locals) v (* we use = here for simplicity, the more general uses D.eqb *)
    | _,_ => False (* one of the call stacks is empty *)
    end.

  (* Defines when a variable v is considered dead *)
  Definition dead_variable (p: CFGProgD.t) (fname: FuncName.t) (bid: BlockID.t) (pc: nat) (v: VarID.t) :=
    forall (st1 st2 st1': StateD.t) (n: nat),
      equiv_states_up_to_v fname bid pc v st1 st2 ->
      SmallStepD.eval n st1 p = Some st1' ->
      exists st2',
        SmallStepD.eval n st2 p = Some st2' /\ equiv_top_frame p st1' st2'.

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
  
  (* This lemma states that live_in provides a sound
  under-approximation of dead variables. The proof uses the
  corresponding (more general) lemma that appears in liveness_snd.v *)
  Lemma live_in_out_snd:  
  forall p fname bid b s,
    CFGProgD.get_block p fname bid = Some b ->
     live_in p fname bid s ->
     forall v, ~ VarSet.In v s -> dead_variable p fname bid 0 v.
  Proof.
    unfold dead_variable.
    intros p fname bid b s H_b_exists H_live_in v H_not_In_v_s st1 st2 st1' n H_st1_equiv_st2 H_eval.

    apply (live_at_pc_zero_eq_live_in p fname bid b s H_b_exists) in H_live_in.

    pose proof (equiv_state_rel p fname bid 0%nat v st1 st2 H_st1_equiv_st2) as H_st1_equiv_st2_gen.
    
    remember (length st1.(StateD.call_stack)) as i eqn:E_i. 
    
    pose proof (live_at_snd p n fname bid b 0%nat s H_b_exists H_live_in st1 st2 st1' v (i-1) H_st1_equiv_st2_gen H_eval H_not_In_v_s) as [st2' [bid' [b' [pc' [s' [H_eval_st2 [H_b'_exists [H_equiv_st1'_st2'_gen H_equiv_top_frame_gen]]]]]]]].

    exists st2'.
    split.
    - apply H_eval_st2.
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
  
  (* This function is the liveness checker, it simply uses the one
  defined in liveness.v --- just to use the same name that is used in
  the paper *)
  Definition liveness_chk (p: CFGProgD.t) (r: prog_live_info_t) :=
    check_program p r.

  (* Just an aliasing of Liveness_sndD.snd_all_blocks_info -- just to
  use the same name that is used in the paper *)
  Definition liveness_info_snd := Liveness_sndD.snd_all_blocks_info.

  (* This proves the soundness and completeness of the checker -- it
  uses the corresponding lemma that appears in liveness_snd.v *)
  Lemma liveness_chk_snd_cmp: 
    forall (p: CFGProgD.t) (r: prog_live_info_t),
      CFGProgD.valid_program p ->
      (liveness_info_snd p r <-> liveness_chk p r = true).
  Proof.
    apply check_valid_prog_correct.
  Qed.
    
End FM26.
