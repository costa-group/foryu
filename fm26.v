Require Import FORYU.state.
Require Import FORYU.program.
Require Import FORYU.semantics.
Require Import FORYU.liveness.
Require Import FORYU.liveness_snd.
Require Import Orders.
Require Import OrdersEx.
Require Import MSets.
Require Import Arith.
Require Import List.
Import ListNotations.
Require Import Coq.Relations.Relation_Operators.
Require Import stdpp.prelude.
Require Import stdpp.relations.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Lia.


Module FM26 (D: DIALECT).

  Module Liveness_sndD := Liveness_snd(D).

  Module LivenessD := Liveness_sndD.LivenessD.
  Module SmallStepD := LivenessD.SmallStepD.
  Module StateD := SmallStepD.StateD.
  Module SmartContractD := SmallStepD.SmartContractD.
  Module FunctionD := SmartContractD.FunctionD.
  Module BlockD := SmartContractD.BlockD.
  Module ExitInfoD := BlockD.ExitInfoD.
  Module InstructionD := BlockD.InstructionD.
  Module YULVariableMapD := BlockD.PhiInfoD.YULVariableMapD.
  Module SimpleExprD := BlockD.PhiInfoD.YULVariableMapD.SimpleExprD.
  Module CallStackD := StateD.CallStackD.
  Module StackFrameD := CallStackD.StackFrameD.
  Module VariableAssignmentD := StackFrameD.VariableAssignmentD.

  Import LivenessD.
  Import Liveness_sndD.


  Definition list_sexp_to_varset (l : list SimpleExprD.t) :=
    (list_to_set (extract_yul_vars l)).
  
  Definition same_pp (fname: FunctionName.t) (bid: BlockID.t) (pc: nat) (sf1 sf2: StackFrameD.t) :=
    sf1.(StackFrameD.function_name) = fname /\ sf2.(StackFrameD.function_name) = fname /\
      sf1.(StackFrameD.curr_block_id) = bid /\ sf2.(StackFrameD.curr_block_id) = bid /\ sf1.(StackFrameD.pc) = pc /\ sf2.(StackFrameD.pc) = pc.

  Definition equiv_frames_up_to_v (fname: FunctionName.t) (bid: BlockID.t) (pc: nat)
    (v: YULVariable.t) (sf1 sf2: StackFrameD.t) :=
    same_pp fname bid pc sf1 sf2 /\
      forall v', v' <> v -> (* equality is required for variable different from v *)
                  VariableAssignmentD.get sf1.(StackFrameD.variable_assignments) v' = VariableAssignmentD.get sf2.(StackFrameD.variable_assignments) v'.
    
  Definition equiv_states_up_to_v (fname: FunctionName.t) (bid: BlockID.t) (pc: nat) (v: YULVariable.t) (st1 st2: StateD.t) :=
    Nat.lt 0 (length (StateD.call_stack st1)) /\
    length (StateD.call_stack st1) = length (StateD.call_stack st2) /\
      st1.(StateD.status) = st2.(StateD.status) /\ st1.(StateD.dialect_state) = st2.(StateD.dialect_state) /\ 
      exists sf1 sf2 rsf,
        st1.(StateD.call_stack) = sf1::rsf /\ st2.(StateD.call_stack) = sf2::rsf /\
          equiv_frames_up_to_v fname bid pc v sf1 sf2.

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
    exists instr,                  (* instr.input are accessed *)
      nth_error b.(BlockD.instructions) pc = Some instr /\
      (VarSet.Equal s (list_sexp_to_varset instr.(InstructionD.input)) )).

  Definition equiv_top_frame (p: SmartContractD.t) (st1 st2: StateD.t) :=
  match st1.(StateD.call_stack), st2.(StateD.call_stack) with
  | nil,nil => True (* both call stacks are empty *)
  | sf1::_,sf2::_ => (* top frames agree on values of accessed variables *)
      let fname := sf1.(StackFrameD.function_name) in
      let bid := sf1.(StackFrameD.curr_block_id) in
      let pc := sf1.(StackFrameD.pc) in
        same_pp fname bid pc sf1 sf2 /\
        forall v s b,
           SmartContractD.get_block p fname bid = Some b ->
           Liveness_sndD.accessed_vars b pc s ->
           VarSet.In v s ->
           VariableAssignmentD.get sf1.(StackFrameD.variable_assignments) v = VariableAssignmentD.get sf2.(StackFrameD.variable_assignments) v
  | _,_ => False (* one of the call stacks is empty *)
 end.

  Definition dead_variable (p: SmartContractD.t) (fname: FunctionName.t) (bid: BlockID.t) (pc: nat) (v: YULVariable.t) :=
    forall (st1 st2 st1': StateD.t) (n: nat),
      equiv_states_up_to_v fname bid pc v st1 st2 ->
      SmallStepD.eval n st1 p = st1' ->
      exists st2',
        SmallStepD.eval n st2 p = st2' /\ equiv_top_frame p st1' st2'.

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
     
    repeat split.
    - lia.
    - apply H_len_call_stack.
    - apply H_status.
    - apply H_dialect.
    -  exists [].
      exists rsf.
      exists sf1.
      exists sf2.
       
      repeat split; try (assumption || lia).       
      + rewrite H_call_stack_st1. simpl. lia.
      + rewrite H_call_stack_st1. simpl. lia.
  Qed.
  
  (*
     This is an instance of the main lemma live_at_snd in liveness_snd.v.
  *)
  Lemma live_in_out_snd:  
  forall p fname bid b s,
    SmartContractD.get_block p fname bid = Some b ->
     live_in p fname bid s ->
     forall v, ~ VarSet.In v s -> dead_variable p fname bid 0 v.
  Proof.
    unfold dead_variable.
    intros p fname bid b s H_b_exists H_live_in v H_not_In_v_s st1 st2 st1' n H_st1_equiv_st2 H_eval.

    rewrite <- live_at_pc_zero_eq_live_in in H_live_in.
    apply (live_at_pc'_0_equiv_live_at_pc_0 p fname bid b s H_b_exists) in H_live_in.

    pose proof (equiv_state_rel p fname bid 0%nat v st1 st2 H_st1_equiv_st2) as H_st1_equiv_st2_gen.
    
    remember (length st1.(StateD.call_stack)) as i eqn:E_i. 
    
    
    pose proof (live_at_snd p n fname bid b 0%nat s H_b_exists H_live_in st1 st2 st1' v (i-1) H_st1_equiv_st2_gen H_eval H_not_In_v_s) as [st2' [pc' [b' [bid' [H_eval_st2 [H_b'_exists [H_equiv_st1'_st2'_gen H_equiv_top_frame_gen]]]]]]].

    exists st2'.
    split.
    - apply H_eval_st2.
    - unfold equiv_vars_in_top_frame in H_equiv_top_frame_gen.
      unfold equiv_top_frame. 
      destruct (StateD.call_stack st1') as [|sf1' rs1']; try assumption.
      destruct (StateD.call_stack st2') as [|sf2' rs2']; try assumption.
      destruct H_equiv_top_frame_gen as [H_fname_sf1'_sf2' [H_bid_sf1'_sf2' [H_pc_sf1'_sf2' H_equiv_varmap]]].
      unfold same_pp.       
      repeat split; try (assumption || intuition).
  Qed.
End FM26.
