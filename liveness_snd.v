Require Import FORYU.state.
Require Import FORYU.program.
Require Import FORYU.semantics.
Require Import FORYU.liveness.
Require Import Orders.
Require Import OrdersEx.
Require Import MSets.
Require Import Arith.
Require Import List.
Import ListNotations.
Require Import Coq.Relations.Relation_Operators.
Require Import stdpp.prelude.
Require Import stdpp.relations. (* This is where nsteps lives *)


Module Liveness_Snd (D: DIALECT).

  Module LivenessD := Liveness(D).
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
  
  Lemma remove_preserves_equal:
    forall s1 s2 e,
      VarSet.Equal s1 s2 ->
      VarSet.Equal (VarSet.remove e s1) (VarSet.remove e s2).
  Proof.
    intros s1 s2 e Heq.
    unfold VarSet.Equal in *.
    intros x.
    repeat rewrite VarSet.remove_spec.
    rewrite Heq.
    reflexivity.
  Qed.

  Lemma add_preserves_equal :
    forall s1 s2 e,
      VarSet.Equal s1 s2 ->
      VarSet.Equal (VarSet.add e s1) (VarSet.add e s2).
  Proof.
    intros s1 s2 e Heq.
    unfold VarSet.Equal in *.
    intros x.
    repeat rewrite VarSet.add_spec.
    rewrite Heq.
    reflexivity.
  Qed.

  Lemma mem_preserves_equal :
    forall s1 s2 e,
      VarSet.Equal s1 s2 ->
      (VarSet.mem e s1) = (VarSet.mem e s2).
  Proof.
    intros s1 s2 e Heq.
    unfold VarSet.Equal in *.
    destruct (VarSet.mem e s1) eqn:H_mem_e_s1; destruct (VarSet.mem e s2) eqn:H_mem_e_s2; try reflexivity.
   
    + rewrite VarSet.mem_spec in H_mem_e_s1.
      rewrite (Heq e) in H_mem_e_s1.
      rewrite <- (VarSet.mem_spec s2 e) in H_mem_e_s1.
      rewrite H_mem_e_s1 in H_mem_e_s2.
      discriminate.

    + rewrite VarSet.mem_spec in H_mem_e_s2.
      rewrite <- (Heq e) in H_mem_e_s2.
      rewrite <- (VarSet.mem_spec s1 e) in H_mem_e_s2.
      rewrite H_mem_e_s2 in H_mem_e_s1.
      discriminate.
  Qed.

  Lemma In_preserves_eq:
    forall s1 s2 v,
      VarSet.Equal s1 s2 ->
      VarSet.In v s1 ->
      VarSet.In v s2.
  Proof.
    intros s1 s2 v H_s1s2 H_In_v_s1.
    rewrite <- VarSet.mem_spec.
    rewrite <- VarSet.mem_spec in H_In_v_s1.
    rewrite <- (mem_preserves_equal s1 s2 v H_s1s2).
    apply H_In_v_s1.
  Qed.

  Lemma not_In_preserves_eq:
    forall s1 s2 v,
      VarSet.Equal s1 s2 ->
      ~VarSet.In v s1 ->
      ~VarSet.In v s2.
  Proof.
    intros s1 s2 v H_s1s2 H_not_In_v_s1.
    rewrite <- VarSet.mem_spec.
    rewrite <- VarSet.mem_spec in H_not_In_v_s1.
    rewrite <- (mem_preserves_equal s1 s2 v H_s1s2).
    apply H_not_In_v_s1.
  Qed.

  Lemma not_In_neq:
    forall x y s,
      VarSet.In x s ->
      ~VarSet.In y s ->
      x<>y.
  Proof.
    intros x y s H_xs H_ys.
    congruence.
  Qed.
      

  Lemma apply_inv_phi_preserves_equal:
    forall l s1 s2,
      VarSet.Equal s1 s2 ->
      VarSet.Equal (apply_inv_phi l s1) (apply_inv_phi l s2).
  Proof.
    induction l as [|a l' IHl'].
    + trivial.
    + intros s1 s2 H_s1_eq_s2.
      unfold apply_inv_phi. fold apply_inv_phi.
      destruct a as [dest orig] eqn:E_do.
      destruct orig as [var|] eqn:E_orig.
      ++ pose proof (VarSet.mem_spec s1 dest) as H_mem_s1.
         pose proof (VarSet.mem_spec s2 dest) as H_mem_s2.
         destruct (VarSet.mem dest s1) eqn:E_mem_dest_s1;
           destruct (VarSet.mem dest s2) eqn:E_mem_dest_s2.
         +++ pose proof (add_preserves_equal (VarSet.remove dest s1) (VarSet.remove dest s2) var (remove_preserves_equal s1 s2 dest H_s1_eq_s2)) as H_add_rem_s1_s2_eq'.
             apply IHl'.
             apply H_add_rem_s1_s2_eq'.
         +++ pose proof (remove_preserves_equal s1 s2 dest H_s1_eq_s2) as H_mem_s1_s2_dest.
             rewrite <- VarSet.mem_spec in *.
             pose proof (mem_preserves_equal s1 s2 dest H_s1_eq_s2) as H_mem_pre_eq.
             rewrite H_mem_pre_eq in E_mem_dest_s1.
             rewrite E_mem_dest_s1  in E_mem_dest_s2.
             discriminate E_mem_dest_s2.
         +++ pose proof (remove_preserves_equal s1 s2 dest H_s1_eq_s2) as H_mem_s1_s2_dest.
             rewrite <- VarSet.mem_spec in *.
             pose proof (mem_preserves_equal s1 s2 dest H_s1_eq_s2) as H_mem_pre_eq.
             rewrite H_mem_pre_eq in E_mem_dest_s1.
             rewrite E_mem_dest_s1  in E_mem_dest_s2.
             discriminate E_mem_dest_s2.
         +++ apply (IHl' s1 s2 H_s1_eq_s2).

      ++ apply IHl'. apply H_s1_eq_s2.
  Qed.

  Lemma diff_preserves_equal:
    forall s1 s1' s2 s2',
      VarSet.Equal s1 s1' ->
      VarSet.Equal s2 s2' ->
      VarSet.Equal (VarSet.diff s1 s2) (VarSet.diff s1' s2').
  Proof.
    intros s1 s1' s2 s2' H_s1_eq_s1' H_s2_eq_s2'.
    unfold VarSet.Equal in *.
    intros x.
    repeat rewrite VarSet.diff_spec.
    rewrite H_s1_eq_s1'.
    rewrite H_s2_eq_s2'.
    reflexivity.
  Qed.

  Lemma union_preserves_equal:
    forall s1 s1' s2 s2',
      VarSet.Equal s1 s1' ->
      VarSet.Equal s2 s2' ->
      VarSet.Equal (VarSet.union s1 s2) (VarSet.union s1' s2').
  Proof.
    intros s1 s1' s2 s2' H_s1_eq_s1' H_s2_eq_s2'.
    unfold VarSet.Equal in *.
    intros x.
    repeat rewrite VarSet.union_spec.
    rewrite H_s1_eq_s1'.
    rewrite H_s2_eq_s2'.
    reflexivity.
  Qed.

  Lemma varset_equal_refl:
    forall s,
      VarSet.Equal s s.
  Proof.
    intro s.
    unfold VarSet.Equal.
    intros x.
    reflexivity.
  Qed.
  
  Lemma varset_equal_sym:
    forall s1 s2,
      VarSet.Equal s1 s2 -> VarSet.Equal s2 s1.
  Proof.
    intros s1 s2 H_s1_eq_s2.
    unfold VarSet.Equal in *.
    intros x.
    rewrite H_s1_eq_s2.
    reflexivity.
  Qed.
  
  Lemma varset_equal_trans:
    forall s0 s1 s2,
      VarSet.Equal s0 s1 ->
      VarSet.Equal s1 s2 ->
      VarSet.Equal s0 s2.
  Proof.
    intros s0 s1 s H_s01 H_s12.
    unfold VarSet.Equal in *.
    intros x.
    rewrite H_s01.
    rewrite H_s12.
    reflexivity.
  Qed.

  Lemma aux {A: Type}:
    forall (n: nat) (l: list A),
      Nat.le (S n) (length l) ->
      exists x xs, l=x::xs.
  Proof.
    intros n l H.
    destruct l as [|x xs].
    - simpl in H.
      pose proof (Nat.nle_succ_0 n) as H0.
      contradiction.
    - exists x. exists xs.
      reflexivity.
  Qed.

  Lemma prop_live_set_bkw_instr_preserves_equal:
    forall i s1 s2,
      VarSet.Equal s1 s2 ->
      VarSet.Equal (prop_live_set_bkw_instr i s1) (prop_live_set_bkw_instr i s2).
  Proof.
    intros l s1 s2 H_eq_s1_s2.
    unfold prop_live_set_bkw_instr.
    apply  (union_preserves_equal (VarSet.diff s1 (list_to_set (InstructionD.output l))) (VarSet.diff s2 (list_to_set (InstructionD.output l))) (list_to_set (extract_yul_vars (InstructionD.input l))) (list_to_set (extract_yul_vars (InstructionD.input l))) (diff_preserves_equal s1 s2 (list_to_set (InstructionD.output l)) (list_to_set (InstructionD.output l)) H_eq_s1_s2 (varset_equal_refl (list_to_set (InstructionD.output l)))) (varset_equal_refl  (list_to_set (extract_yul_vars (InstructionD.input l))))).
  Qed.

  Lemma prop_live_set_bkw_aux_preserves_equal:
    forall n l s1 s2,
      VarSet.Equal s1 s2 ->
      VarSet.Equal (prop_live_set_bkw_aux n l s1) (prop_live_set_bkw_aux n l s2).
  Proof.
    induction n as [|n' IHn'].
    - simpl.
      intros l s1 s2 H_eq_s1_s2.
      apply H_eq_s1_s2.
    - intros l s1 s2 H_eq_s1_s2.
      destruct l as [|i l'] eqn:E_l; try discriminate.
      + simpl.
        apply H_eq_s1_s2.
      +
        simpl.
        apply (IHn' l' (prop_live_set_bkw_instr i s1) (prop_live_set_bkw_instr i s2) (prop_live_set_bkw_instr_preserves_equal i s1 s2 H_eq_s1_s2)).
  Qed.

  Lemma prop_live_set_bkw_is_prop_aux:
    forall l s,
      prop_live_set_bkw l s = prop_live_set_bkw_aux (length l) (rev l) s.
  Proof.
    intros l s.
    destruct l as [|i l'] eqn:E_l.
    - simpl. reflexivity.
    - unfold prop_live_set_bkw. reflexivity.
  Qed.
  
  Lemma prop_live_set_bkw_preserves_equal:
    forall l s1 s2,
      VarSet.Equal s1 s2 ->
      VarSet.Equal (prop_live_set_bkw l s1) (prop_live_set_bkw l s2).
  Proof.
    intros l s1 s2 H_eq_s1_s2.
    repeat rewrite prop_live_set_bkw_is_prop_aux.
    apply (prop_live_set_bkw_aux_preserves_equal (Datatypes.length l) (rev l) s1 s2 H_eq_s1_s2).
  Qed.

  Definition add_jump_var_if_applicable (b: BlockD.t) (s: VarSet.t) :=
    match b.(BlockD.exit_info) with
    | ExitInfoD.ConditionalJump cond_var _ _ => VarSet.add cond_var s
    | _ => s
      end.
  
  (*
    The following co-inductive defintions are for live variables properties.
    
    live_out p f bid s: s is the set of live variables at the exit of the block p/f/bid
    live_in p f bid s: s is the set of live variables at the entry of the block p/f/bid
   *)
  CoInductive live_out  (p : SmartContractD.t) : FunctionName.t -> BlockID.t -> VarSet.t -> Prop :=

  (* Return block *)
  | lo_block_w_ret (fname : FunctionName.t) (bid :  BlockID.t) (b: BlockD.t) (rs: list SimpleExprD.t) (sout: VarSet.t):
    SmartContractD.get_block p fname bid = Some b -> (* the block exists *)
    BlockD.is_return_block b = Some rs -> (* it is an exit block and rs is the list of returned expressions *)
    VarSet.Equal sout (list_to_set (extract_yul_vars rs)) ->
    live_out p fname bid sout

  (* Terminated block *)
  | lo_block_w_ter (fname : FunctionName.t) (bid :  BlockID.t) (b: BlockD.t) (sout: VarSet.t) :
    SmartContractD.get_block p fname bid = Some b -> (* the block exists *)
    BlockD.is_terminated_block b = true -> (* it is an terminate block *)
    VarSet.Equal sout VarSet.empty ->
    live_out p fname bid sout

  (* A block with a with jump *)
  | lo_block_w_jump (fname : FunctionName.t) (bid next_bid:  BlockID.t) (b next_b: BlockD.t) (s: VarSet.t) (sout: VarSet.t):
    SmartContractD.get_block p fname bid = Some b -> (* the block exists *)
    BlockD.is_jump_block b = Some next_bid -> (* the block ends with a jump, and next_bid is the id of the next block *)
    live_in p fname next_bid s -> (* s is the set of live variables at the entry of p/fname/next_bid *)
    SmartContractD.get_block p fname next_bid = Some next_b -> (* next_b is the block with id next_bid *)
    VarSet.Equal sout (apply_inv_phi (BlockD.phi_function next_b bid) s) ->
    live_out p fname bid sout  (* sout is the set of live variable at the exit of p/fname/bid *)

  (* A block with a conditional jump *)
  | lo_block_w_cond_jump (fname : FunctionName.t) (bid next_bid_if_true next_bid_if_false:  BlockID.t) (cond_var: nat) (b next_b_if_true next_b_if_false: BlockD.t) (s1 s2 sout: VarSet.t):
    SmartContractD.get_block p fname bid = Some b -> (* the block exists *)
    BlockD.is_cond_jump_block b = Some (cond_var, next_bid_if_true, next_bid_if_false) -> (* the block ends with a conditional jump, and next_bid_if_true and next_bid_if_false are the identifiers of the next blocks *)
    live_in p fname next_bid_if_true s1 ->  (* s1 is the set of live at the entry of p/fname/next_bid_if_true *)
    live_in p fname next_bid_if_false s2 -> (* s2 is the set of live variables at the entry of p/fname/next_bid_if_false *)
    SmartContractD.get_block p fname next_bid_if_true = Some next_b_if_true -> (* next_b_if_true is the block with id next_bid_if_true *)
    SmartContractD.get_block p fname next_bid_if_false = Some next_b_if_false -> (* next_b_if_false is the block with id next_bid_if_false *)
    VarSet.Equal sout (VarSet.union (apply_inv_phi (BlockD.phi_function next_b_if_true bid) s1) (apply_inv_phi (BlockD.phi_function next_b_if_false bid) s2)) ->
    live_out p fname bid sout
  with
    live_in (p : SmartContractD.t) : FunctionName.t -> BlockID.t -> VarSet.t -> Prop :=
  | li_block_any (fname : FunctionName.t) (bid :  BlockID.t) (b: BlockD.t) (s sout: VarSet.t):
    SmartContractD.get_block p fname bid = Some b -> (* the block exists *)
    live_out p fname bid s -> (* s is the set of live variables at the exit of p/fname/bid *)
    VarSet.Equal sout (prop_live_set_bkw b.(BlockD.instructions) (add_jump_var_if_applicable b s)) ->
    live_in p fname bid sout.

  Inductive live_at_pc (p : SmartContractD.t) : FunctionName.t -> BlockID.t -> nat -> VarSet.t -> Prop :=
  | live_at_pc_1 (fname : FunctionName.t) (bid :  BlockID.t) (b: BlockD.t) (pc: nat) (s sout: VarSet.t):
    SmartContractD.get_block p fname bid = Some b -> (* the block exists *)
    live_out p fname bid s ->
    Nat.le pc (length b.(BlockD.instructions)) ->
    VarSet.Equal sout (prop_live_set_bkw_aux ((length b.(BlockD.instructions)) - pc) (rev b.(BlockD.instructions)) (add_jump_var_if_applicable b s)) ->
    live_at_pc p fname bid pc sout.

  Inductive live_at_pc' (p : SmartContractD.t) : FunctionName.t -> BlockID.t -> nat -> VarSet.t -> Prop :=
  | live_at_pc'_eob (fname : FunctionName.t) (bid :  BlockID.t) (b: BlockD.t) (pc: nat) (s sout: VarSet.t):
    SmartContractD.get_block p fname bid = Some b -> (* the block exists *)
    live_out p fname bid s ->
    pc = (length b.(BlockD.instructions)) ->
    VarSet.Equal sout (add_jump_var_if_applicable b s) ->
    live_at_pc' p fname bid pc sout
  | live_at_pc'_inb (fname : FunctionName.t) (bid :  BlockID.t) (b: BlockD.t) (pc: nat) (s sout: VarSet.t) (i: InstructionD.t):  
    SmartContractD.get_block p fname bid = Some b -> (* the block exists *)
    live_at_pc' p fname bid (S pc) s ->
    Nat.lt pc (length b.(BlockD.instructions)) ->
    nth_error b.(BlockD.instructions) pc = Some i ->
    VarSet.Equal sout (prop_live_set_bkw_instr i s) ->
    live_at_pc' p fname bid pc sout.

  Lemma len_eq:
    forall {A: Type} (x y : list A), x = y -> length x = length y.
  Proof.
    intros.
    rewrite H.
    reflexivity.
  Qed.
  
    
  Theorem live_at_pc'_equiv_live_at_pc:
    forall i p fname bid b s,
      SmartContractD.get_block p fname bid = Some b -> (* the block exists *)
      Nat.le i (length b.(BlockD.instructions)) ->
      live_at_pc p fname bid ((length b.(BlockD.instructions)) - i) s <-> live_at_pc' p fname bid ((length b.(BlockD.instructions)) - i) s.
  Proof.
    Admitted.
    
  Theorem live_at_pc_zero_eq_live_in:
    forall p fname bid s,
      live_at_pc p fname bid 0%nat s <-> live_in p fname bid s.
  Proof.
    intros p fname bid s.
    remember 0%nat as pc eqn:H_pc_0.
    split.
    - intros H_live_at_pc.
      destruct H_live_at_pc.
      subst pc.
      rewrite Nat.sub_0_r in H2.
      destruct (BlockD.instructions b) eqn:H_instrs.
      + pose proof (@li_block_any p fname bid b s sout H H0).
        rewrite H_instrs in H3.
        simpl in *.
        apply (H3 H2).
      + pose proof (@li_block_any p fname bid b s sout H H0).
        pose proof (prop_live_set_bkw_is_prop_aux (t :: l) (add_jump_var_if_applicable b s)).
        rewrite H_instrs in H3.
        rewrite H4 in H3.
        apply (H3 H2).
    - intro H_live_in.
      destruct H_live_in.
      
      pose proof (live_at_pc_1 p fname bid b 0 s sout H H0 (le_0_n (Datatypes.length (BlockD.instructions b)))).

      rewrite prop_live_set_bkw_is_prop_aux in H1.
      rewrite Nat.sub_0_r in H2.
      rewrite H_pc_0.
      apply (H2 H1).
  Qed.

  Lemma live_in_varset_eq:
    forall p f bid s1 s2,
      VarSet.Equal s1 s2 ->
      live_in p f bid s1 ->
      live_in p f bid s2.
  Proof.
    intros p f bid s1 s2 H_s1_eq_s2 H_live_in_s1.
    destruct H_live_in_s1.
    apply (@li_block_any p fname bid b s s2 H H0 (varset_equal_trans s2 sout (prop_live_set_bkw (BlockD.instructions b) (add_jump_var_if_applicable b s)) (varset_equal_sym sout s2 H_s1_eq_s2) H1)).    
  Qed.

  Lemma live_out_varset_eq:
    forall p f bid s1 s2,
      VarSet.Equal s1 s2 ->
      live_out p f bid s1 ->
      live_out p f bid s2.
  Proof.
    intros p f bid s1 s2 H_s1_eq_s2 H_live_out_s1.
    destruct H_live_out_s1 eqn:E_live_out.

    + apply (@lo_block_w_ret p fname bid b rs s2 e e0 (varset_equal_trans s2 sout (list_to_set (extract_yul_vars rs)) (varset_equal_sym sout s2 H_s1_eq_s2) e1)).

    + apply (@lo_block_w_ter p fname bid b s2 e e0 (varset_equal_trans s2 sout VarSet.empty (varset_equal_sym sout s2 H_s1_eq_s2) e1)).

    + apply (@lo_block_w_jump p fname bid next_bid b next_b s s2 e e0 l e1 (varset_equal_trans s2 sout (apply_inv_phi (BlockD.phi_function next_b bid) s) (varset_equal_sym sout s2 H_s1_eq_s2) e2)).

    + apply (@lo_block_w_cond_jump p fname bid next_bid_if_true next_bid_if_false cond_var b next_b_if_true next_b_if_false s1 s0 s2 e e0 l l0 e1 e2 (varset_equal_trans s2 sout (VarSet.union (apply_inv_phi (BlockD.phi_function next_b_if_true bid) s1) (apply_inv_phi (BlockD.phi_function next_b_if_false bid) s0)) (varset_equal_sym sout s2 H_s1_eq_s2) e3)).
  Qed.


  (* All block have live-variable results in r *)
  Definition snd_res_for_all_blocks (p : SmartContractD.t)  (r: sc_live_info_t) : Prop :=
    forall bid f b,
      SmartContractD.get_block p f bid = Some b -> 
      exists bid_res fr,
        r f = Some fr /\ fr bid = bid_res.

  (*
     This defines a proposition stating that the live-variable
     information for p/f/bid in 'r' exists, and it is sound.

     Soundness here means that some relations between the in/out
     information of each block holds. It is pretty much follows what
     is defined in the definition of live_in/live_out/etc. But we do
     not use those defintions yet, they will be used lated to prove
     that if 'r' is sound of all blocks, then live_in/live_out holds
     for all blocks etc.
   *)
  Definition snd_block_out_info (p : SmartContractD.t) (r: sc_live_info_t) (f: FunctionName.t) (b: BlockD.t) : Prop :=
    exists f_info b_in_info b_out_info,
      (r f) = Some f_info /\ (* The live-variable information of the function exists *)
        f_info b.(BlockD.bid) = Some (b_in_info,b_out_info) /\ (* The live-variable information of the block exists *)
        match b.(BlockD.exit_info) with
        | ExitInfoD.Terminated =>
            VarSet.Equal b_out_info  VarSet.empty 
        | ExitInfoD.ReturnBlock rs => 
            VarSet.Equal b_out_info (list_to_set (extract_yul_vars rs))
        | ExitInfoD.Jump next_bid =>
            exists next_b next_b_in_info next_b_out_info,
            SmartContractD.get_block p f next_bid = Some next_b /\ 
              f_info next_bid = Some (next_b_in_info,next_b_out_info) /\
              VarSet.Equal b_out_info (apply_inv_phi (BlockD.phi_function next_b b.(BlockD.bid)) next_b_in_info)
        | ExitInfoD.ConditionalJump cond_var next_bid_if_true next_bid_if_false => 
            exists next_b_if_true next_b_ift_in_info next_b_ift_out_info next_b_if_false next_b_iff_in_info next_b_iff_out_info,
            SmartContractD.get_block p f next_bid_if_true = Some next_b_if_true /\ 
            SmartContractD.get_block p f next_bid_if_false = Some next_b_if_false /\ 
              f_info next_bid_if_true = Some (next_b_ift_in_info,next_b_ift_out_info) /\
              f_info next_bid_if_false = Some (next_b_iff_in_info,next_b_iff_out_info) /\
              VarSet.Equal b_out_info (VarSet.union
                                         (apply_inv_phi (BlockD.phi_function next_b_if_true b.(BlockD.bid)) next_b_ift_in_info)
                                         (apply_inv_phi (BlockD.phi_function next_b_if_false b.(BlockD.bid)) next_b_iff_in_info))
        end.
 
  Definition snd_block_in_info (r: sc_live_info_t) (f: FunctionName.t) (b: BlockD.t) : Prop :=
    exists f_info b_in_info b_out_info,
      (r f) = Some f_info /\ (* The live-variable information of the function exists *)
        f_info b.(BlockD.bid) = Some (b_in_info,b_out_info) /\ (* The live-variable information of the block exists *)
        VarSet.Equal b_in_info (prop_live_set_bkw b.(BlockD.instructions) (add_jump_var_if_applicable b b_out_info)).
  
  Definition snd_block_info (p : SmartContractD.t) (r: sc_live_info_t) (f: FunctionName.t) (b: BlockD.t)
    : Prop :=
    snd_block_in_info r f b /\ snd_block_out_info p r f b.
  

  Definition snd_all_blocks_info (p : SmartContractD.t) (r: sc_live_info_t) : Prop :=
    forall fname bid b,
      SmartContractD.get_block p fname bid = Some b -> (* if the block exists *)
      snd_block_info p r fname b. (* it has sound information *)


  Lemma bid_b:
    forall p f bid b,
      SmartContractD.get_block p f bid = Some b -> (BlockD.bid b) = bid.
  Proof.
    intros p f bid b H_exists.
    unfold SmartContractD.get_block in H_exists.
    destruct (SmartContractD.get_function p f) as [func|]; try discriminate.
    unfold SmartContractD.FunctionD.get_block in H_exists.
    destruct (find (fun b : SmartContractD.FunctionD.BlockD.t => BlockID.eqb (SmartContractD.FunctionD.BlockD.bid b) bid) (SmartContractD.FunctionD.blocks func)) as [block|] eqn:H_find; try discriminate.
    apply find_some in H_find.
    destruct H_find as [_ H_find].
    unfold BlockID.eqb in H_find.
    rewrite Nat.eqb_eq in H_find.
    injection H_exists as H_t0_b.
    rewrite H_t0_b in H_find.
    apply H_find.
  Qed.

  
  Lemma exit_info_vs_is_cond_jump:
    forall b cond_var target_if_true target_if_false,
      BlockD.exit_info b =
        BlockD.ExitInfoD.ConditionalJump cond_var target_if_true target_if_false ->
      BlockD.is_cond_jump_block b = Some (cond_var, target_if_true, target_if_false).
  Proof.
    intros b cond_var target_if_true target_if_false H.
    unfold BlockD.is_cond_jump_block.
    rewrite H.
    reflexivity.
  Qed.

  Lemma exit_info_vs_is_jump:
    forall b target,
      BlockD.exit_info b =
        BlockD.ExitInfoD.Jump target ->
      BlockD.is_jump_block b = Some target.
  Proof.
    intros b target H.
    unfold BlockD.is_jump_block.
    rewrite H.
    reflexivity.
  Qed.

  Lemma exit_info_vs_is_return:
    forall b rs,
      BlockD.exit_info b =
        BlockD.ExitInfoD.ReturnBlock rs ->
      BlockD.is_return_block b = Some rs.
  Proof.
    intros b rs H.
    unfold BlockD.is_return_block.
    rewrite H.
    reflexivity.
  Qed.

  Lemma exit_info_vs_is_terminated:
    forall b,
      BlockD.exit_info b =
        BlockD.ExitInfoD.Terminated ->
      BlockD.is_terminated_block b = true.
  Proof.
    intros b H.
    unfold BlockD.is_terminated_block.
    rewrite H.
    reflexivity.
  Qed.
  

  CoFixpoint build_live_in (p : SmartContractD.t) (f: FunctionName.t) (bid: BlockID.t) (b: BlockD.t)
    (r: sc_live_info_t) (f_info: fun_live_info_t) (b_in_info b_out_info: VarSet.t)
    (H_snd_info: snd_all_blocks_info p r) (H_b_exists: SmartContractD.get_block p f bid = Some b)
    (H_f_info: (r f) = Some f_info) (H_b_info: f_info bid = Some (b_in_info,b_out_info)) : live_in p f bid b_in_info
  with build_live_out (p : SmartContractD.t) (f: FunctionName.t) (bid: BlockID.t) (b: BlockD.t)
         (r: sc_live_info_t) (f_info: fun_live_info_t) (b_in_info b_out_info: VarSet.t)
                           (H_snd_info: snd_all_blocks_info p r) (H_b_exists: SmartContractD.get_block p f bid = Some b)
                           (H_f_info: (r f) = Some f_info) (H_b_info: f_info bid = Some (b_in_info,b_out_info)) : live_out p f bid b_out_info.
  Proof.
    (* the case of live_in p f bid b_in_info *)
    - unfold snd_all_blocks_info in H_snd_info.
      pose proof (H_snd_info f bid b H_b_exists) as H_snd_b_info.
      unfold snd_block_info in H_snd_b_info.
      destruct H_snd_b_info as [H_snd_b_in_info H_snd_b_out_info].
      unfold snd_block_in_info in H_snd_b_in_info.
      destruct H_snd_b_in_info as [f_info' [b_in_info' [b_out_info' [H_r_f [H_f_info' H_b_in_info']]]]].
      rewrite (bid_b p f bid b H_b_exists) in H_f_info'.
      
      assert (H_f_info_info': f_info = f_info').
      (*{*)
        rewrite H_f_info in H_r_f. injection H_r_f as H_r_f. apply H_r_f.
      (*}*)

      assert (H_b_in_info_info': b_in_info = b_in_info').
      (*{*)
      rewrite <- H_f_info_info' in H_f_info'. rewrite H_b_info in H_f_info'. injection H_f_info' as H_b_in_info_info' H_b_out_info_info'. rewrite H_b_in_info_info'. reflexivity.
      (*{*)

      assert (H_b_out_info_info': b_out_info = b_out_info').
      (*{*)
      rewrite <- H_f_info_info' in H_f_info'. rewrite H_b_info in H_f_info'. injection H_f_info' as _ H_b_out_info_info'. rewrite H_b_out_info_info'. reflexivity.
      (*}*)

      rewrite H_b_in_info_info'.

      apply (@li_block_any p f bid b b_out_info' b_in_info' H_b_exists).

      apply (build_live_out p f bid b r f_info' b_in_info' b_out_info' H_snd_info H_b_exists H_r_f  H_f_info').
      
      apply H_b_in_info'.            
        
    (* the case of live_out p f bid b_in_info *)
    - pose proof (H_snd_info f bid b H_b_exists) as H_snd_b_info.
      unfold snd_block_info in H_snd_b_info.
      destruct H_snd_b_info as [H_snd_b_in_info H_snd_b_out_info].
      unfold snd_block_out_info in H_snd_b_out_info.
      destruct H_snd_b_out_info as [f_info' [b_in_info' [b_out_info' [H_r_f [H_f_info' H_b_out_info']]]]].
      rewrite (bid_b p f bid b H_b_exists) in H_f_info'.
  
      assert (H_f_info_info': f_info = f_info').
      (*{*)
      rewrite H_f_info in H_r_f. injection H_r_f as H_r_f. apply H_r_f.
      (*{*)

      rewrite (bid_b p f bid b H_b_exists) in H_b_out_info'.

      assert (H_b_out_info_info': b_out_info = b_out_info').
      (*{*)
      rewrite <- H_f_info_info' in H_f_info'. rewrite H_b_info in H_f_info'. injection H_f_info' as _ H_b_out_info_info'. rewrite H_b_out_info_info'. reflexivity.
      (*{*)
             
      destruct b.(BlockD.exit_info) as [cond_var target_if_true target_if_false | target | return_values | ] eqn:E_exit_info.

      (* conditional jump *)
      + destruct H_b_out_info' as [next_b_if_true [ next_b_ift_in_info [next_b_ift_out_info [next_b_if_false [ next_b_iff_in_info [next_b_iff_out_info [H_b_next_ift_exists [H_b_next_iff_exists [H_f_ift_info' [H_f_iff_info' H_b_out_info']]]]]]]]]].

      rewrite H_b_out_info_info'.
      
      apply  (@lo_block_w_cond_jump p f bid target_if_true target_if_false cond_var b next_b_if_true next_b_if_false next_b_ift_in_info next_b_iff_in_info b_out_info' H_b_exists (exit_info_vs_is_cond_jump b cond_var target_if_true target_if_false E_exit_info) (build_live_in p f target_if_true next_b_if_true r f_info' next_b_ift_in_info next_b_ift_out_info H_snd_info H_b_next_ift_exists H_r_f H_f_ift_info') (build_live_in p f target_if_false next_b_if_false r f_info' next_b_iff_in_info next_b_iff_out_info H_snd_info H_b_next_iff_exists H_r_f H_f_iff_info') H_b_next_ift_exists H_b_next_iff_exists H_b_out_info').

      (* jump *)
      + destruct H_b_out_info' as [next_b [next_b_in_info [next_b_out_info [H_b_next_exists [H_f_next_b_info' H_next_b_out_info']]]]].

      rewrite H_b_out_info_info'.

      apply (@lo_block_w_jump p f bid target b next_b next_b_in_info b_out_info' H_b_exists (exit_info_vs_is_jump b target E_exit_info) (build_live_in p f target next_b r f_info' next_b_in_info next_b_out_info H_snd_info H_b_next_exists H_r_f H_f_next_b_info') H_b_next_exists H_next_b_out_info').

      (* return *)
      + rewrite H_b_out_info_info'.
        apply (@lo_block_w_ret p f bid b return_values b_out_info' H_b_exists (exit_info_vs_is_return b return_values E_exit_info ) H_b_out_info').

      (* teminated *)
      + rewrite H_b_out_info_info'.
        apply (@lo_block_w_ter p f bid b b_out_info' H_b_exists (exit_info_vs_is_terminated b E_exit_info) H_b_out_info' ).
  Defined.

  Lemma snd_all_blocks_info_to_bid_info:
    forall (p : SmartContractD.t) (r: sc_live_info_t),
      snd_all_blocks_info p r ->  
      forall f bid b,
        SmartContractD.get_block p f bid = Some b ->
        exists f_info b_in_info b_out_info,
          (r f) = Some f_info /\
            f_info bid = Some (b_in_info,b_out_info).
    Proof.
      intros p r H_snd_info f bid b H_b_exists.
      pose proof (H_snd_info f bid b H_b_exists) as H_b_info_snd.
      unfold snd_block_info in  H_b_info_snd.
      destruct H_b_info_snd as [H_b_in_info_snd _].
      unfold snd_block_in_info in H_b_in_info_snd.
      rewrite (bid_b p f bid b H_b_exists) in H_b_in_info_snd.
      destruct H_b_in_info_snd as [f_info [b_in_info [b_out_info [H_r_f [H_f_info _]]]]].
      exists f_info. exists b_in_info. exists b_out_info.
      split; assumption.
    Qed.

  Theorem snd_info:
    forall (p : SmartContractD.t) (r: sc_live_info_t),
      snd_all_blocks_info p r ->  
      forall f bid b,
        SmartContractD.get_block p f bid = Some b ->
        exists f_info b_in_info b_out_info,
          (r f) = Some f_info /\
            f_info bid = Some (b_in_info,b_out_info) /\
            live_in p f bid b_in_info /\
            live_out p f bid b_out_info.
  Proof.
    intros p r H_snd_info f bid b H_b_exists.
    pose proof (H_snd_info f bid b H_b_exists) as H_b_info_snd.
    unfold snd_block_info in  H_b_info_snd.
    destruct H_b_info_snd as [H_b_in_info_snd H_b_out_info_snd].
    pose proof (snd_all_blocks_info_to_bid_info p r H_snd_info f bid b H_b_exists) as H_snd_all_blocks_info_to_bid_info.
    destruct H_snd_all_blocks_info_to_bid_info as [f_info [b_in_info [b_out_info [H_r_f H_f_info]]]].
    exists f_info. exists b_in_info. exists b_out_info.
    repeat split.
    - assumption.
    - assumption.
    - apply (build_live_in p f bid b r f_info b_in_info b_out_info H_snd_info H_b_exists H_r_f H_f_info).
    - apply (build_live_out p f bid b r f_info b_in_info b_out_info H_snd_info H_b_exists H_r_f H_f_info).
  Qed.
    
  
  Lemma check_live_in_snd:
    forall r f b,
      check_live_in r f b = true -> snd_block_in_info r f b.
  Proof.
    intros r f b H_check_live_in.
    unfold check_live_in in H_check_live_in.
    destruct (r f) as [f_info|] eqn:E_r_f; try discriminate.
    destruct (f_info (BlockD.bid b)) as [b_info|] eqn:E_f_info_b; try discriminate.
    destruct b_info as [b_in_info b_out_info].
    unfold snd_block_in_info.
    exists f_info. exists b_in_info. exists b_out_info.
    split; try assumption.
    split; try assumption.
    rewrite <- VarSet.equal_spec.
    apply H_check_live_in.
  Qed.

  Lemma check_live_in_complete:
    forall r f b,
      snd_block_in_info r f b -> check_live_in r f b = true.
  Proof.
    intros r f b H_snd.
    unfold snd_block_in_info in H_snd.
    destruct H_snd as [f_info [b_in_info [b_out_info [H_r_f [H_f_info H_eq]]]]].
    unfold check_live_in.
    destruct (r f) as [f_info'|]; try discriminate.
    injection H_r_f as H_f_info_info'.
    rewrite H_f_info_info'.
    rewrite H_f_info.
    rewrite VarSet.equal_spec.
    apply H_eq.
  Qed.

  Lemma check_live_in_correct:
    forall r f b,
      snd_block_in_info r f b <-> check_live_in r f b = true.
  Proof.
    intros r f b.
    split.
    + apply check_live_in_complete.
    + apply check_live_in_snd.
  Qed.


  Lemma check_live_out_snd:
    forall p r f b,
      check_live_out p r f b = true -> snd_block_out_info p r f b.
  Proof.
    intros p r f b H_check_live_out.
    unfold check_live_out in H_check_live_out.
    destruct (r f) as [f_info|] eqn:E_r_f; try discriminate.
    destruct (f_info (BlockD.bid b)) as [b_info|] eqn:E_f_info_b; try discriminate.
    destruct b_info as [b_in_info b_out_info].
    unfold snd_block_out_info.
    exists f_info. exists b_in_info. exists b_out_info.
    split; try assumption.
    split; try assumption.
    destruct (BlockD.exit_info b) as [cond_var target_if_true target_if_false|next_bid|rs|] eqn:E_b_exit_info.

    + destruct (SmartContractD.get_block p f target_if_true) as [next_b_if_true|]; try discriminate.
      destruct (SmartContractD.get_block p f target_if_false) as [next_b_if_false|]; try discriminate.
      destruct (f_info target_if_true) as [target_if_true_info|]; try discriminate.
      destruct target_if_true_info as [next_b_ift_in_info next_b_ift_out_info].
      destruct (f_info target_if_false) as [target_if_false_info|]; try discriminate.
      destruct target_if_false_info as [next_b_iff_in_info next_b_iff_out_info].

      exists next_b_if_true. exists next_b_ift_in_info. exists next_b_ift_out_info.
      exists next_b_if_false. exists next_b_iff_in_info. exists next_b_iff_out_info.
      split; try reflexivity.
      split; try reflexivity.
      split; try reflexivity.
      split; try reflexivity.
      rewrite <- VarSet.equal_spec.
      apply H_check_live_out.

    + destruct (SmartContractD.get_block p f next_bid) as [next_b|]; try discriminate.
      destruct (f_info next_bid) as [next_bid_info|]; try discriminate.
      destruct next_bid_info as [next_b_in_info next_b_out_info].
      exists next_b. exists next_b_in_info. exists next_b_out_info.
      split; try reflexivity.
      split; try reflexivity.
      rewrite <- VarSet.equal_spec.
      apply H_check_live_out.

    + rewrite <- VarSet.equal_spec.
      apply H_check_live_out.

    + rewrite <- VarSet.equal_spec.
      apply H_check_live_out.
  Qed.
  
Lemma check_live_out_complete:
    forall p r f b,
      snd_block_out_info p r f b -> check_live_out p r f b = true.
  Proof.
    intros p r f b H_snd.
    unfold snd_block_out_info in H_snd.
    destruct H_snd as [f_info [b_in_info [b_out_info [H_r_f [H_f_info H_eq]]]]].
    unfold check_live_out.
    rewrite H_r_f.
    rewrite H_f_info.

    destruct (BlockD.exit_info b) as [cond_var target_if_true target_if_false|next_bid|rs|] eqn:E_b_exit_info.

    + destruct H_eq as [next_b_if_true [next_b_ift_in_info [next_b_ift_out_info [next_b_if_false [next_b_iff_in_info [next_b_iff_out_info [H_b_true_exists [H_b_false_exists [if_true_info [if_false_info H_eq]]]]]]]]]].

      rewrite H_b_true_exists.
      rewrite H_b_false_exists.
      rewrite if_true_info.
      rewrite if_false_info.
      rewrite VarSet.equal_spec.
      apply H_eq.

    + destruct H_eq as [next_b [next_b_in_info [next_b_out_info [H_b_next_exists [H_next_b_f_info' H_eq]]]]].
      rewrite H_b_next_exists.
      rewrite H_next_b_f_info'.
      rewrite VarSet.equal_spec.
      apply H_eq.

    + rewrite VarSet.equal_spec.
      apply H_eq.
    + rewrite VarSet.equal_spec.
      apply H_eq.
  Qed.
  
  Lemma check_live_out_correct:
    forall p r f b,
      snd_block_out_info p r f b <-> check_live_out p r f b = true.
  Proof.
    intros p r f b.
    split.
    + apply check_live_out_complete.
    + apply check_live_out_snd.
  Qed.

  Lemma check_live_snd:
    forall p r f b,
      check_live p r f b = true -> snd_block_info p r f b.
  Proof.
    intros p r f b H_check_live.
    unfold check_live in H_check_live.
    destruct (check_live_in r f b) eqn:E_check_live; try discriminate.
    unfold snd_block_info.
    split.
    + apply (check_live_in_snd r f b E_check_live).
    + apply (check_live_out_snd p r f b H_check_live).
  Qed.

  Lemma check_live_complete:
    forall p r f b,
      snd_block_info p r f b -> check_live p r f b = true.
  Proof.
    intros p r f b H_snd.
    unfold snd_block_info in H_snd.
    destruct H_snd as [H_snd_in H_snd_out].
    unfold check_live.
    rewrite (check_live_in_complete r f b H_snd_in).
    rewrite (check_live_out_complete p r f b H_snd_out).
    reflexivity.
  Qed.

  Lemma check_live_correct:
    forall p r f b,
      snd_block_info p r f b <-> check_live p r f b = true.
  Proof.
    intros p r f b.
    split.
    + apply check_live_complete.
    + apply check_live_snd.
  Qed.

  Lemma check_blocks_snd:
    forall bs fname p r,
      check_blocks bs fname p r = true ->
      forall b,
        In b bs -> snd_block_info p r fname b.
  Proof.
    induction bs as [|b bs' IHbs'].
    - simpl. intros fname p r H_chk b H_False.
      destruct H_False.
    - intros fname p r H_chk b0 H_in_b0_bbs'.
      simpl check_blocks in H_chk.
      destruct (check_live p r fname b) eqn:E_check_live; try discriminate.
      simpl in H_in_b0_bbs'.
      destruct H_in_b0_bbs' as [H_b_eq_b0 | H_in_b0_bs'].

      + subst b0.
        apply (check_live_snd p r fname b E_check_live).
      + apply (IHbs' fname p r H_chk b0 H_in_b0_bs').
  Qed.
    
  Lemma in_cons_if_prop:
    forall {A: Type} (b : A) (bs: list A) (P: A->Prop),
      (forall e, In e (b::bs) -> P e) ->
      (forall e, In e bs -> P e).
  Proof.
    intros A b bs P H.
    intro f.
    pose proof (H f) as H'.
    simpl in H'.
    intros H''.
    apply H'.
    right.
    apply H''.
  Qed.

  Lemma check_blocks_complete:
    forall bs fname p r,
      (forall b, In b bs -> snd_block_info p r fname b) ->
      check_blocks bs fname p r = true.
  Proof.
    induction bs as [|b bs' IHbs'].    
    - simpl. intros fname p r H_snd.
      reflexivity.
    - intros fname p r H_snd.
      pose proof (H_snd b (in_eq b bs')) as H_snd_b.
      simpl.
      destruct (check_live p r fname b) eqn:E_check_live.
      + apply (IHbs' fname p r (@in_cons_if_prop BlockD.t b bs' (fun b => snd_block_info p r fname b) H_snd)).
      + rewrite (check_live_complete p r fname b H_snd_b) in E_check_live.
        discriminate E_check_live.
  Qed.
  
  Lemma check_blocks_correct:
    forall bs fname p r,
      (forall b, In b bs -> snd_block_info p r fname b) <->
          check_blocks bs fname p r = true.
  Proof.
    intros bs fname p r.
    split.
    - apply (check_blocks_complete bs fname p r).
    - apply (check_blocks_snd bs fname p r).
  Qed.
  
  Lemma check_functions_snd:
    forall fs p r,
    check_functions fs p r = true ->
      forall f,
        In f fs -> forall b, In b f.(FunctionD.blocks) -> snd_block_info p r f.(FunctionD.name) b.
  Proof.
    induction fs as [|f fs' IHfs'].
    - simpl.
      intros p r H_check_functions f H_False.
      destruct H_False.
    - intros p r H_check_functions f0 H_in_f0_ffs' b H_in_b_blocks_f0.
      simpl in H_in_f0_ffs'.
      destruct H_in_f0_ffs' as [H_f_eq_f0 | H_in_f0_fs'].
      + subst f0.
        simpl check_functions in H_check_functions.
        destruct (check_blocks (FunctionD.blocks f) (FunctionD.name f) p r) eqn:E_check_f; try discriminate.
        apply (check_blocks_snd (FunctionD.blocks f) (FunctionD.name f) p r E_check_f b H_in_b_blocks_f0).
      + simpl in H_check_functions.
        destruct (check_blocks (FunctionD.blocks f) (FunctionD.name f)); try discriminate.
        apply (IHfs' p r H_check_functions f0 H_in_f0_fs' b H_in_b_blocks_f0).
  Qed.

  
  Lemma check_functions_complete:
    forall fs p r,
      (forall f, 
          In f fs -> forall b, In b f.(FunctionD.blocks) -> snd_block_info p r f.(FunctionD.name) b) ->
      check_functions fs p r = true.
  Proof.
    induction fs as [|f fs' IHfs'].
    - simpl.
      intros p r H_snd.
      reflexivity.
    - intros p r H_snd.
      pose proof (H_snd f) as  H_snd_f.
      simpl.
      destruct (check_blocks (FunctionD.blocks f) (FunctionD.name f) p r) eqn:E_check_f_blocks.
      + apply IHfs'.
        intros f0 H_in_f0_fs' b.
        apply (H_snd f0 (in_cons f f0 fs' H_in_f0_fs') b).
      + rewrite (check_blocks_complete (FunctionD.blocks f) (FunctionD.name f) p r (H_snd_f (in_eq f fs'))) in E_check_f_blocks.
        discriminate E_check_f_blocks.
  Qed.
  
  Lemma check_smart_contract_snd:
    forall p r,
    check_smart_contract p r = true ->
    forall f,
        In f p.(SmartContractD.functions) -> forall b, In b f.(FunctionD.blocks) -> snd_block_info p r f.(FunctionD.name) b.
  Proof.
    intros p r H_check_sc.
    intros f H_in_f_pfs b H_b_in_bsf.
    unfold check_smart_contract in H_check_sc.
    apply (check_functions_snd (SmartContractD.functions p) p r H_check_sc f H_in_f_pfs b H_b_in_bsf).
  Qed.
    

  Lemma check_smart_contract_complete:
    forall p r,
      (forall f,
          In f p.(SmartContractD.functions) -> forall b, In b f.(FunctionD.blocks) -> snd_block_info p r f.(FunctionD.name) b) ->
      check_smart_contract p r = true.
  Proof.
    intros p r H_snd.
    unfold check_smart_contract.
    apply (check_functions_complete (SmartContractD.functions p) p r H_snd).
  Qed.

  Lemma check_smart_contract_correct:
    forall p r,
      (forall f,
          In f p.(SmartContractD.functions) -> forall b, In b f.(FunctionD.blocks) -> snd_block_info p r f.(FunctionD.name) b) <->check_smart_contract p r = true.
    Proof.
      intros p r.
      split.
      - apply check_smart_contract_complete.
      - apply check_smart_contract_snd.
    Qed.

  Lemma check_valid_smart_contract_correct:
    forall p r,
      SmartContractD.valid_smart_contract p ->
      snd_all_blocks_info p r <-> check_smart_contract p r = true.
  Proof.
    intros p r H_valid_p.
    rewrite <- check_smart_contract_correct.
    unfold snd_all_blocks_info.
    split.
    - intro H_get_block_imp_snd.
      pose proof (SmartContractD.valid_p_vs_get_block p H_valid_p) as H_valid_p_vs_get_block.

      intros f H_f_in_pfs b H_b_in_fbs.
      apply (H_get_block_imp_snd (FunctionD.name f) (BlockD.bid b) b).
      rewrite H_valid_p_vs_get_block.
      exists f.
      
      repeat split.
      + apply H_f_in_pfs.
      + apply H_b_in_fbs.
      + unfold FunctionName.eqb. rewrite String.eqb_eq. reflexivity.
      + unfold BlockID.eqb. rewrite Nat.eqb_eq. reflexivity.          

    - intros H_snd.
      intros fname bid b H_get_block.

      rewrite (SmartContractD.valid_p_vs_get_block p H_valid_p fname bid b) in H_get_block.

      destruct H_get_block as [f [H_f_in_pfs [H_b_in_fbs [H_f_name_eqb_fname H_b_bid_eqb_bid]]]].
      unfold FunctionName.eqb in H_f_name_eqb_fname.
      rewrite String.eqb_eq in H_f_name_eqb_fname.
      subst fname.
      
      apply (H_snd f H_f_in_pfs b H_b_in_fbs).
  Qed.


  (* (R_step p) is a transition relation induced by to SmallStepD.step *)
  Definition R_step (p: SmartContractD.t) : relation StateD.t :=
    fun st st' => SmallStepD.step st p = st'.

  (* (R_trans p) is a transitive closure of (R_step p) *)
  Definition R_step_trans (p: SmartContractD.t) : relation StateD.t :=
    tc (R_step p).

  (* (R_step_trans_refl_n p) is an indexed transitive closure of (R_step p).
     It is reflexive, so we always have to avoid the 0 case.
  *)
  Definition R_step_trans_refl_n (p: SmartContractD.t) :=
    nsteps (R_step p).
  
  Definition running_state (s: StateD.t) :=
    s.(StateD.status) = Status.Running.
  
  Definition same_function_call (s1 s2: StateD.t) :=
    match s1.(StateD.call_stack),s2.(StateD.call_stack) with
    |  sf1::rs1,sf2::rs2 => FunctionName.eqb sf1.(StackFrameD.function_name) sf2.(StackFrameD.function_name) = true /\ rs1 = rs2
    |  _,_ => False
    end.


  (*
  [f3,f2,f1,f0]    <- l
  [f3,f2,f1]+f0::[]  i = 0
  [f3,f2]+f1::[f0]   i = 1
  [f3]+f2::[f1,f0]   i = 2
  []+f3::[f2,f1,f0]  i = 3
   *)             
  Definition split_at_i {A : Type} (i: nat) (l hl tl: list A) (a: A) :=
      Nat.lt i (length l) /\ l = hl++(a::tl) /\ length tl = i.

  Lemma n_eq_n_plus_m:
    forall n m, n = m+n -> m=0.
  Proof.
    induction n as [|n' IHn'].
    - intros m H.
      rewrite <- plus_n_O in H.
      symmetry in H.
      apply H.
    - intros m H.
      rewrite Nat.add_comm in H.
      rewrite plus_Sn_m in H.
      injection H as H.
      rewrite Nat.add_comm in H.
      apply (IHn' m H).
  Qed.

  Lemma split_at_len_l_tl_nil {A:Type} :
    forall(l hl tl: list A) (a: A),
      split_at_i 0 l hl tl a -> tl = [].
  Proof.
    intros l hl tl a H.
    unfold split_at_i in H.
    destruct H as [H_lt_0_len_l [H_l H_len_tl]].
    apply nil_length_inv in H_len_tl.
    apply H_len_tl.
  Qed.

  Lemma split_at_len_l_hl {A:Type} :
    forall(l hl tl: list A) (a: A),
      split_at_i ((length l)-1) l hl tl a -> hl = [].
  Proof.
    intros l hl tl a H_split.
    unfold split_at_i in H_split.

    destruct H_split as [H_len_l [H_l H_i]].
    rewrite H_l in H_i.
    rewrite length_app in H_i.
    simpl in H_i.
    rewrite <- plus_n_Sm in H_i.
    simpl in H_i.
    rewrite Nat.sub_0_r in H_i.
    apply n_eq_n_plus_m  in H_i.
    apply nil_length_inv in H_i.
    apply H_i.
  Qed.
          

  Definition accessed_vars (b: BlockD.t) (pc: nat) (s: VarSet.t) :=
    ( pc = (length b.(BlockD.instructions)) /\
        match b.(BlockD.exit_info) with
        | ExitInfoD.ConditionalJump cv _ _ => (VarSet.Equal s (VarSet.add cv VarSet.empty))
        | ExitInfoD.ReturnBlock rvs => (VarSet.Equal s (list_to_set (extract_yul_vars rvs)))
        | _ => VarSet.Equal s VarSet.empty
        end
    )
    \/
    (  pc < (length b.(BlockD.instructions)) /\
         exists i,
           nth_error b.(BlockD.instructions) pc = Some i /\
             (VarSet.Equal s (list_to_set (extract_yul_vars i.(InstructionD.input)))) 
    ).
      
  Definition equiv_vars_in_top_frame (b: BlockD.t) (pc: nat) (st1 st2: StateD.t) :=
    match st1.(StateD.call_stack), st2.(StateD.call_stack) with
    | nil,nil => True
    | sf1::_,sf2::_ =>
        sf1.(StackFrameD.function_name) = sf2.(StackFrameD.function_name) /\
        sf1.(StackFrameD.curr_block_id) = sf2.(StackFrameD.curr_block_id) /\
        sf1.(StackFrameD.pc) = sf2.(StackFrameD.pc) /\
        sf1.(StackFrameD.return_variables) = sf2.(StackFrameD.return_variables) /\
        forall v s,
          accessed_vars b pc s ->
          VarSet.In v s ->
          VariableAssignmentD.get sf1.(StackFrameD.variable_assignments) v =
            VariableAssignmentD.get sf2.(StackFrameD.variable_assignments) v
    | _,_ => False
    end.

  Lemma equiv_vars_in_top_frame_refl:
    forall b pc st,
      equiv_vars_in_top_frame b pc st st.
  Proof.
    intros b pc st.
    unfold equiv_vars_in_top_frame.
    destruct (StateD.call_stack st) as [|sf rsf].
    - apply I.
    - repeat split; try reflexivity.
  Qed.
  
  Definition equiv_stack_frames_up_to_v (fname: FunctionName.t) (bid: BlockID.t) (pc: nat) (v: YULVariable.t) (sf1 sf2: StackFrameD.t) :=
    sf1.(StackFrameD.function_name) = fname /\
      sf1.(StackFrameD.curr_block_id) = bid /\
      sf1.(StackFrameD.pc) = pc /\ 
      sf2.(StackFrameD.function_name) = fname /\
      sf2.(StackFrameD.curr_block_id) = bid /\
      sf2.(StackFrameD.pc) = pc /\ 
      sf1.(StackFrameD.return_variables) = sf2.(StackFrameD.return_variables) /\
      forall v', v'<>v ->
                 VariableAssignmentD.get sf1.(StackFrameD.variable_assignments) v' =
                   VariableAssignmentD.get sf2.(StackFrameD.variable_assignments) v'.
  
  Definition equiv_states_up_to_i_v (p: SmartContractD.t) (i: nat) (fname: FunctionName.t) (bid: BlockID.t) (pc: nat) (v: YULVariable.t) (st1 st2: StateD.t) :=
    let call_stack1 := st1.(StateD.call_stack) in
    let call_stack2 := st2.(StateD.call_stack) in
    Nat.lt i (length call_stack1) /\
      (length call_stack1) = (length call_stack2) /\
      st1.(StateD.status) = st2.(StateD.status) /\
      st1.(StateD.dialect_state) = st2.(StateD.dialect_state) /\
      exists hl tl sf1 sf2,
        split_at_i i call_stack1 hl tl sf1 /\
          split_at_i i call_stack2 hl tl sf2 /\
          equiv_stack_frames_up_to_v fname bid pc v sf1 sf2.

  Lemma varset_in_dec:
    forall x s,
      VarSet.In x s \/ ~VarSet.In x s.
  Proof.
    intros x s.
    destruct (VarSet.mem x s) eqn:E_mem.
    - left.
      rewrite VarSet.mem_spec in E_mem.
      apply E_mem.
    - right.
      intro H_contra.
      rewrite <- VarSet.mem_spec in H_contra.
      rewrite H_contra in E_mem.
      discriminate E_mem.
  Qed.
    
  Lemma not_In_cons {A: Type}:
    forall (l: list A) (a b: A),
      ~ In a (b::l) ->
      ~ In a l.
  Proof.
    intros l a b H_not_in.
    simpl in H_not_in.
    intro H_contra.
    apply H_not_in.
    right.
    apply H_contra.
  Qed.
  
  Lemma not_In_neq_first {A: Type}:
    forall (l: list A) (a b: A),
      ~ In a (b::l) -> a <> b.
  Proof.
    intros l a b H_not_in.
    simpl in H_not_in.
    intro H_contra.
    apply H_not_in.
    left.
    symmetry.
    apply H_contra.
  Qed.
    
  Lemma eval_input_snd:
    forall l fname bid pc v sf1 sf2,
      equiv_stack_frames_up_to_v fname bid pc v sf1 sf2 ->
      ~List.In (inl v) l ->
      SmallStepD.eval_input l sf1 = 
        SmallStepD.eval_input l sf2.
  Proof.
    induction l as [ | e l'].
    - intros fname bid pc v sf1 sf2 H_eq_sf1_sf2 H_not_in.
      simpl.
      reflexivity.
    - intros fname bid pc v sf1 sf2 H_eq_sf1_sf2 H_not_in.
      simpl.
      destruct e as [var | val] eqn:E_e.
      
      + pose proof ( IHl' fname bid pc v sf1 sf2 H_eq_sf1_sf2 (not_In_cons l' (inl v) (inl var) H_not_in)) as IH_l'.
        rewrite IH_l'.
        unfold equiv_stack_frames_up_to_v in H_eq_sf1_sf2.
        pose proof (not_In_neq_first l' (inl v) (inl var ) H_not_in) as H_v_neq_var_inl.
        assert (H_var_neq_v: var <> v ). 
        {
          intro H_contra.
          apply H_v_neq_var_inl.
          rewrite H_contra.
          reflexivity.
        }.
        destruct H_eq_sf1_sf2 as [_ [_ [_ [_ [_ [_ [_ H_eq_sf1_sf2]]]]]]].
        rewrite (H_eq_sf1_sf2 var H_var_neq_v).
        reflexivity.
      + pose proof ( IHl' fname bid pc v sf1 sf2 H_eq_sf1_sf2 (not_In_cons l' (inl v) (inr val) H_not_in)) as IH_l'.
        rewrite IH_l'.
        reflexivity.
  Qed.
  
  Lemma get_next_instruction_succ:
    forall st p instruction sf rsf b,
      st.(StateD.call_stack) = sf::rsf ->
      SmartContractD.get_block p sf.(StackFrameD.function_name) sf.(StackFrameD.curr_block_id) = Some b ->
      SmallStepD.get_next_instruction st p = Some instruction ->
      Nat.lt sf.(StackFrameD.pc) (length b.(BlockD.instructions)).
  Proof.
    intros st p instruction sf rsf b H_call_stack H_block_exists H_get_next.
    unfold SmallStepD.get_next_instruction in H_get_next.
    rewrite H_call_stack in H_get_next.
    unfold SmallStepD.SmartContractD.get_instruction in H_get_next.
    rewrite H_block_exists in H_get_next.
    pose proof (nth_error_Some (SmallStepD.SmartContractD.BlockD.instructions b) (SmallStepD.StackFrameD.pc sf)).
    
    assert (nth_error (SmallStepD.SmartContractD.BlockD.instructions b) (SmallStepD.StackFrameD.pc sf) <> None).
    {
      intros H_contra.
      rewrite H_contra in H_get_next.
      discriminate H_get_next.
    }.
    
    rewrite H in H0.
    apply H0.
  Qed.

  Lemma equiv_states_eq_status:
    forall p i fname bid pc v st1 st2,
      equiv_states_up_to_i_v p i fname bid pc v st1 st2 ->
      st1.(StateD.status) = st2.(StateD.status).
  Proof.
    intros p i fname bid pc v st1 st2 H_equiv_st1_st2.
    apply H_equiv_st1_st2.
  Qed.

  Lemma equiv_state_equiv_frames_at_top:
    forall p fname bid b pc i v s st1 st2,
      SmartContractD.get_block p fname bid = Some b  ->
      live_at_pc' p fname bid pc s ->
      ~ VarSet.In v s ->
      equiv_states_up_to_i_v p i fname bid pc v st1 st2 ->
      equiv_vars_in_top_frame b pc st1 st2.
  Proof.
    intros p fname bid b pc i v s st1 st2 H_exists_b H_live_at_pc H_not_In_v_s H_eq_st1_st2.

    unfold equiv_states_up_to_i_v in H_eq_st1_st2.
    destruct H_eq_st1_st2 as [H_lt_i [H_len_st1_st2 [_ [_ [ hl [tl [sf1 [sf2 [H_split_i_st1 [H_split_i_st2 H_equiv_frame_up_to_v_sf1_sf2]]]]]]]]]].
    destruct hl as [|sftop] eqn:E_hl.
    - unfold split_at_i in H_split_i_st1.
      destruct H_split_i_st1 as [_ H_call_stack_st1].
      unfold split_at_i in H_split_i_st2.
      destruct H_split_i_st2 as [_ H_call_stack_st2].
      simpl in H_call_stack_st1.
      simpl in H_call_stack_st2.
      destruct H_call_stack_st1 as [H_call_stack_st1 _].
      destruct H_call_stack_st2 as [H_call_stack_st2 _].
    
      unfold equiv_vars_in_top_frame.
      rewrite H_call_stack_st1.
      rewrite H_call_stack_st2.      
      unfold equiv_stack_frames_up_to_v in H_equiv_frame_up_to_v_sf1_sf2.
      destruct H_equiv_frame_up_to_v_sf1_sf2 as [H_fname_sf1 [H_bid_sf1 [H_sf1_pc [H_fname_sf2 [H_bid_sf2 [H_pc_sf2 [H_ret_vars H_eq_assgin_up_to_v]]]]]]].
      subst fname.
      subst bid.
      subst pc.

      repeat split.
      + apply (symmetry H_fname_sf2).
      + apply (symmetry H_bid_sf2).
      + apply (symmetry H_pc_sf2).
      + apply H_ret_vars.
      + intros v0 s0 H_acc H_v0_not_In_s0.
        unfold accessed_vars in H_acc.
        destruct H_acc as [ [H_pc_sf1_eq_len H_match]| [H_pc_sf1 H_args]].
        
        * destruct (BlockD.exit_info b) as [cv | | rvs | ] eqn:E_b_exit.
          ** destruct H_live_at_pc.
             *** unfold add_jump_var_if_applicable in H2.
                 rewrite H_exists_b in H.
                 injection H as H.
                 subst b0.
                 rewrite E_b_exit in H2.
                 pose proof (In_preserves_eq s0 (VarSet.add cv VarSet.empty) v0 H_match H_v0_not_In_s0).
                 unfold VarSet.Equal in H_match.

                 rewrite (VarSet.add_spec) in H.
                 destruct H.
                 **** subst v0.
                      pose proof (not_In_preserves_eq  sout (VarSet.add cv s) v H2 H_not_In_v_s) as H_not_In_v_add_cv_s.
                      rewrite VarSet.add_spec in H_not_In_v_add_cv_s.
                      apply Decidable.not_or in H_not_In_v_add_cv_s.
                      destruct H_not_In_v_add_cv_s.
                      assert(cv<>v). intro. contradiction (symmetry H4).
                      apply (H_eq_assgin_up_to_v cv H4).
                 **** pose proof (VarSet.empty_spec).
                      unfold VarSet.Empty in H3.
                      pose proof (H3 v0) as H3.
                      contradiction.
             *** rewrite H_exists_b in H.
                 injection H as H.
                 subst b0.
                 rewrite H_pc_sf1_eq_len in H0.
                 contradiction (Nat.lt_irrefl (length (BlockD.instructions b))).
          ** pose proof (In_preserves_eq s0 VarSet.empty v0 H_match H_v0_not_In_s0).
            pose proof (VarSet.empty_spec).
            unfold VarSet.Empty in H0.
            pose proof (H0 v0) as H0.
            contradiction.
          ** destruct H_live_at_pc.
             *** destruct H0.
                 **** rewrite H_exists_b in H0.
                      injection H0 as H0.
                      rewrite H_exists_b in H.
                      injection H as H.
                      subst b0.
                      subst b1.
                      unfold BlockD.is_return_block in H3.
                      rewrite E_b_exit in H3.
                      injection H3 as H3.
                      subst rs.
                      unfold add_jump_var_if_applicable in H2.
                      rewrite E_b_exit in H2.
                      rewrite H4 in H2.

                      pose proof (In_preserves_eq  s0 (list_to_set (extract_yul_vars rvs)) v0 H_match H_v0_not_In_s0).
                      pose proof (not_In_preserves_eq  sout (list_to_set (extract_yul_vars rvs)) v H2 H_not_In_v_s).                      
                      pose proof (not_In_neq v0 v (list_to_set (extract_yul_vars rvs)) H H0).
                      apply (H_eq_assgin_up_to_v v0 H3).
                 **** unfold BlockD.is_terminated_block in H3.
                      rewrite H_exists_b in H0.
                      injection H0 as H0.
                      rewrite H_exists_b in H.
                      injection H as H.
                      subst b0.
                      subst b1.
                      rewrite E_b_exit in H3.
                      discriminate H3.
                     
                 **** unfold BlockD.is_jump_block in H3.
                      rewrite H_exists_b in H0.
                      injection H0 as H0.
                      rewrite H_exists_b in H.
                      injection H as H.
                      subst b0.
                      subst b1.
                      rewrite E_b_exit in H3.
                      discriminate H3.
                      
                 **** unfold BlockD.is_cond_jump_block in H3.
                      rewrite H_exists_b in H0.
                      injection H0 as H0.
                      rewrite H_exists_b in H.
                      injection H as H.
                      subst b0.
                      subst b1.
                      rewrite E_b_exit in H3.
                      discriminate H3.
             *** rewrite H_exists_b in H.
                 injection H as H.
                 subst b0.
                 rewrite H_pc_sf1_eq_len in H0.
                 contradiction (Nat.lt_irrefl (length (BlockD.instructions b))).

          ** pose proof (In_preserves_eq s0 VarSet.empty v0 H_match H_v0_not_In_s0).
             pose proof (VarSet.empty_spec).
             unfold VarSet.Empty in H0.
             pose proof (H0 v0) as H0.
             contradiction.

        * destruct H_args as [instr [H_nth_err H_s0]].
          destruct H_live_at_pc.

          ** rewrite H_exists_b in H.
             injection H as H.
             subst b0.
             rewrite H1 in H_pc_sf1.
             contradiction (Nat.lt_irrefl (length (BlockD.instructions b))).

          ** rewrite H_exists_b in H.
             injection H as H.
             subst b0.
             rewrite H_nth_err in H1.
             injection H1 as H1.
             subst i0.
             unfold prop_live_set_bkw_instr in H2.
             pose proof (not_In_preserves_eq sout (VarSet.union (VarSet.diff s (list_to_set (InstructionD.output instr))) (list_to_set (extract_yul_vars (InstructionD.input instr)))) v H2 H_not_In_v_s).
             rewrite VarSet.union_spec in H.
             apply Decidable.not_or in H.
             destruct H.
             pose proof (In_preserves_eq s0 (list_to_set (extract_yul_vars (InstructionD.input instr))) v0 H_s0 H_v0_not_In_s0).
             pose proof (not_In_neq v0 v (list_to_set (extract_yul_vars (InstructionD.input instr))) H3 H1).
             apply (H_eq_assgin_up_to_v v0 H4).

    - unfold split_at_i in H_split_i_st1.
      destruct H_split_i_st1 as [_ [H_split_i_st1 _]].
      simpl in H_split_i_st1.
      unfold split_at_i in H_split_i_st2.
      destruct H_split_i_st2 as [_ [H_split_i_st2 _]].
      simpl in H_split_i_st2.

      unfold equiv_vars_in_top_frame.
      rewrite H_split_i_st1.
      rewrite H_split_i_st2.
      repeat split; try reflexivity.
  Qed.

  Lemma get_next_instr_eq_states:
    forall p i fname bid pc v st1 st2,
      equiv_states_up_to_i_v p i fname bid pc v st1 st2 ->
      SmallStepD.get_next_instruction st1 p = SmallStepD.get_next_instruction st2 p. 
  Proof.
    intros p i fname bid pc v st1 st2 H_eq_st1_st2.
    unfold SmallStepD.get_next_instruction.
    unfold equiv_states_up_to_i_v in H_eq_st1_st2.
    destruct H_eq_st1_st2 as [H_lt_i [H_len_call_stack_eq [_ [_ [hl [tl [sf1 [sf2 [H_split_i_st1 [H_split_i_st2 H_equiv_up_to_v_sf1_sf2]]]]]]]]]].
    unfold split_at_i in H_split_i_st1.
    destruct H_split_i_st1 as [_ [H_call_stack_st1 _]].
    unfold split_at_i in H_split_i_st2.
    destruct H_split_i_st2 as [_ [H_call_stack_st2 _]].
    destruct hl as [|sftop] eqn:E_hl.
    - simpl in H_call_stack_st1.
      simpl in H_call_stack_st2.
      rewrite H_call_stack_st1.
      rewrite H_call_stack_st2.
      unfold equiv_stack_frames_up_to_v in H_equiv_up_to_v_sf1_sf2.
      destruct H_equiv_up_to_v_sf1_sf2 as [H_fname_sf1 [H_bid_sf1 [H_pc_sf1 [H_fname_sf2 [H_bid_sf2 [H_pc_sf2 _]]]]]].
      rewrite H_fname_sf1.
      rewrite H_bid_sf1.
      rewrite H_pc_sf1.
      rewrite H_fname_sf2.
      rewrite H_bid_sf2.
      rewrite H_pc_sf2.
      reflexivity.
    - simpl in H_call_stack_st1.
      simpl in H_call_stack_st2.
      rewrite H_call_stack_st1.
      rewrite H_call_stack_st2.
      reflexivity.
  Qed.
      
  Lemma live_at_exec_inst_snd:   
    forall (p: SmartContractD.t) (i: nat) (fname: FunctionName.t) (bid: BlockID.t) (b: BlockD.t) (pc: nat) (s: VarSet.t) (instr: InstructionD.t),
      SmartContractD.get_block p fname bid = Some b ->
      live_at_pc' p fname bid pc s ->
      forall  (st1 st2 st1': StateD.t) (v: YULVariable.t),
        equiv_states_up_to_i_v p i fname bid pc v st1 st2 ->
        SmallStepD.execute_instr instr st1 p = st1' ->
        ~ VarSet.In v s ->
        exists st2' bid' b' pc' s',
          SmallStepD.execute_instr instr st2 p = st2'
          /\
          SmartContractD.get_block p fname bid' = Some b'  /\ 
          (
           ( ( equiv_states_up_to_i_v p i fname bid' pc' v st1' st2') /\ live_at_pc' p fname bid' pc' s' /\ ~ VarSet.In v s' )
           \/
           st2' = st1'
          )
          /\
          equiv_vars_in_top_frame b' pc' st1' st2'.
  Proof.
    Admitted.

    Lemma live_at_handle_block_finish_snd:   
    forall (p: SmartContractD.t) (i: nat) (fname: FunctionName.t) (bid: BlockID.t) (b: BlockD.t) (pc: nat) (s: VarSet.t),
      SmartContractD.get_block p fname bid = Some b ->
      live_at_pc' p fname bid pc s ->
      forall  (st1 st2 st1': StateD.t) (v: YULVariable.t),
        equiv_states_up_to_i_v p i fname bid pc v st1 st2 ->
        SmallStepD.handle_block_finish st1 p = st1' ->
        ~ VarSet.In v s ->
        exists st2' bid' b' pc' s',
          SmallStepD.handle_block_finish st2 p = st2'
          /\
          SmartContractD.get_block p fname bid' = Some b'  /\ 
          (
           ( ( equiv_states_up_to_i_v p i fname bid' pc' v st1' st2') /\ live_at_pc' p fname bid' pc' s' /\ ~ VarSet.In v s' )
           \/
           st2' = st1'
          )
          /\
          equiv_vars_in_top_frame b' pc' st1' st2'.
  Proof.
    Admitted.

  
  Lemma live_at_step_snd:   
    forall (p: SmartContractD.t) (i: nat) (fname: FunctionName.t) (bid: BlockID.t) (b: BlockD.t) (pc: nat) (s: VarSet.t),
      SmartContractD.get_block p fname bid = Some b ->
      live_at_pc' p fname bid pc s ->
      forall  (st1 st2 st1': StateD.t) (v: YULVariable.t),
        equiv_states_up_to_i_v p i fname bid pc v st1 st2 ->
        SmallStepD.step st1 p = st1' ->
        ~ VarSet.In v s ->
        exists st2' bid' b' pc' s',
          SmallStepD.step st2 p = st2'
          /\
            SmartContractD.get_block p fname bid' = Some b'  /\ 
            (
              ( ( equiv_states_up_to_i_v p i fname bid' pc' v st1' st2') /\ live_at_pc' p fname bid' pc' s' /\ ~ VarSet.In v s' )
              \/
                st2' = st1'
            )
          /\
            equiv_vars_in_top_frame b' pc' st1' st2'.
  Proof.
    intros p i fname bid b pc s H_exists_b H_live_at_pc st1 st2 st1' v H_equiv_up_to_i_v_st1_st2 H_step_st1 H_not_In_v_s.
    unfold SmallStepD.step in H_step_st1.
    destruct (SmallStepD.StateD.status st1) eqn:E_status_st1.
    
    - unfold SmallStepD.step.
      pose proof (equiv_states_eq_status p i fname bid pc v st1 st2 H_equiv_up_to_i_v_st1_st2) as H_eq_states.
      rewrite H_eq_states in E_status_st1.
      rewrite E_status_st1.
      
      destruct (SmallStepD.get_next_instruction st1 p) as [instr|] eqn:E_get_instr_st1.
      
      + pose proof (get_next_instr_eq_states p i fname bid pc v st1 st2 H_equiv_up_to_i_v_st1_st2) as H_get_instr_st2.
        rewrite E_get_instr_st1 in H_get_instr_st2.
        rewrite <- H_get_instr_st2.
        
        apply (live_at_exec_inst_snd p i fname bid b pc s instr H_exists_b H_live_at_pc st1 st2 st1' v H_equiv_up_to_i_v_st1_st2 H_step_st1 H_not_In_v_s ).
        
      + pose proof (get_next_instr_eq_states p i fname bid pc v st1 st2 H_equiv_up_to_i_v_st1_st2) as H_get_instr_st2.
        rewrite E_get_instr_st1 in H_get_instr_st2.
        rewrite <- H_get_instr_st2.
        
        apply (live_at_handle_block_finish_snd p i fname bid b pc s H_exists_b H_live_at_pc st1 st2 st1' v H_equiv_up_to_i_v_st1_st2 H_step_st1 H_not_In_v_s ).
        
    (* Not running state -- it is copied 3 times for 3 cases, should define a strategy *)
    - subst st1'.
      pose proof (equiv_states_eq_status p i fname bid pc v st1 st2 H_equiv_up_to_i_v_st1_st2) as H_eq_status.
      unfold SmallStepD.step.
      rewrite <- H_eq_status.
      rewrite E_status_st1.
      exists st2.
      exists bid.
      exists b.
      exists pc.
      exists s.
      repeat split; try (reflexivity || assumption).
      + left.
        split.
        * assumption.
        * split.
          ** assumption.
          ** assumption.
      + apply (equiv_state_equiv_frames_at_top  p fname bid b pc i v s st1 st2 H_exists_b H_live_at_pc H_not_In_v_s H_equiv_up_to_i_v_st1_st2).

    - subst st1'.
      pose proof (equiv_states_eq_status p i fname bid pc v st1 st2 H_equiv_up_to_i_v_st1_st2) as H_eq_status.
      unfold SmallStepD.step.
      rewrite <- H_eq_status.
      rewrite E_status_st1.
      exists st2.
      exists bid.
      exists b.
      exists pc.
      exists s.
      repeat split; try (reflexivity || assumption).
      + left.
        split.
        * assumption.
        * split.
          ** assumption.
          ** assumption.
      + apply (equiv_state_equiv_frames_at_top  p fname bid b pc i v s st1 st2 H_exists_b H_live_at_pc H_not_In_v_s H_equiv_up_to_i_v_st1_st2).

    - subst st1'.
      pose proof (equiv_states_eq_status p i fname bid pc v st1 st2 H_equiv_up_to_i_v_st1_st2) as H_eq_status.
      unfold SmallStepD.step.
      rewrite <- H_eq_status.
      rewrite E_status_st1.
      exists st2.
      exists bid.
      exists b.
      exists pc.
      exists s.
      repeat split; try (reflexivity || assumption).
      + left.
        split.
        * assumption.
        * split.
          ** assumption.
          ** assumption.
      + apply (equiv_state_equiv_frames_at_top  p fname bid b pc i v s st1 st2 H_exists_b H_live_at_pc H_not_In_v_s H_equiv_up_to_i_v_st1_st2).
  Qed.
    
  Lemma live_at_snd:   
    forall (p: SmartContractD.t) (n: nat) (fname: FunctionName.t) (bid: BlockID.t) (b: BlockD.t) (pc: nat) (s: VarSet.t),
      SmartContractD.get_block p fname bid = Some b ->
      live_at_pc' p fname bid pc s ->
      forall  (st1 st2 st1': StateD.t) (v: YULVariable.t) (i: nat),
        equiv_states_up_to_i_v p i fname bid pc v st1 st2 ->
        SmallStepD.eval n st1 p = st1' ->
        ~ VarSet.In v s ->
        exists st2' pc' b' bid',
          SmallStepD.eval n st2 p = st2' /\
            (equiv_states_up_to_i_v p i fname bid' pc' v st1' st2' \/ st2' = st1') /\
            equiv_vars_in_top_frame b' pc' st1' st2'.
  Proof.
    intros p.
    induction n as [|n' IHn'].
    - intros fname bid b pc s H_b_exists H_live_at_pc st1 st2 st1' v i H_equiv_st1_st2 H_eval_st1 H_not_In_v_s.
      simpl in H_eval_st1.
      simpl.
      exists st2.
      exists pc.
      exists b.
      exists bid.
      repeat split.
      +  left.
         rewrite <- H_eval_st1.
         apply H_equiv_st1_st2.
      + rewrite <- H_eval_st1.
        apply (equiv_state_equiv_frames_at_top p fname bid b pc i v s st1 st2 H_live_at_pc H_not_In_v_s H_equiv_st1_st2).

    - intros fname bid b pc s H_b_exists H_live_at_pc st1 st2 st1' v i H_equiv_st1_st2 H_eval_st1 H_not_In_v_s.

      simpl in H_eval_st1.
      remember (SmallStepD.step st1 p) as st1_1_step eqn:H_step_st1.
      symmetry in H_step_st1.
      
      pose proof (live_at_step_snd p i fname bid b pc s H_b_exists H_live_at_pc st1 st2 st1_1_step v H_equiv_st1_st2 H_step_st1 H_not_In_v_s) as H_live_at_step_snd.
      simpl.
      destruct H_live_at_step_snd as [st2_1_step [bid' [b' [pc' [s' [H_step_st2 [ H_exists_b' [[[ H_equiv_states_up_to_i_v_st1_1_step_st2_1_step [H_live_at_pc'_bid'_pc' H_v_not_In_s']] | H_st2_1_step_eq_st1_1_step] H_equiv_vars_in_top_frame_st1_1_step_st2_1_step]]]]]]]].

      + pose proof (IHn' fname bid' b' pc' s' H_exists_b' H_live_at_pc'_bid'_pc' st1_1_step st2_1_step st1' v i H_equiv_states_up_to_i_v_st1_1_step_st2_1_step H_eval_st1 H_v_not_In_s') as IHn'_inst.
        destruct IHn'_inst as [st2' [pc'' [b'' [bid'' [H_eval_st2_1_step [H_equiv_st1'_st2' H_equiv_vars_in_top_frame_st1'_st2']]]]]].

        exists st2'.
        exists pc''.
        exists b''.
        exists bid''.
        repeat split.

        * rewrite H_step_st2.
          apply H_eval_st2_1_step.
        * apply H_equiv_st1'_st2'.
        * apply H_equiv_vars_in_top_frame_st1'_st2'.

      + subst st2_1_step.
        exists st1'.
        exists pc'.
        exists b'.
        exists bid'.
        repeat split.
        
        * rewrite H_st2_1_step_eq_st1_1_step.
          apply H_eval_st1.
        * right. reflexivity.
        * apply equiv_vars_in_top_frame_refl.
  Qed.

(*  
Definition dead_variable  (p: SmartContractD.t) (fname: FunctionName.t) (bid: BlockID.t) (b: BlockD.t) (pc: nat) (v: YULVariable.t) :=
  forall (st1 st1': StateD.t) (n i: nat),
     stack_frame_i_at_pp i fname bid pc st1 ->
     SmallStepD.eval n st1 p = st1' ->
     forall st2,
        equiv_states_up_to_i_v p i v st1 st2->
        exists st2',
           SmallStepD.eval n st2 p = st2' /\
           (equiv_states_up_to_i_v p i v st1' st2' \/ st2' = st1') /\
           equiv_vars_in_top_frame b pc st1' st2'.

 
  Theorem live_at_snd_2:   
    forall (p: SmartContractD.t) (fname: FunctionName.t) (bid: BlockID.t) (b: BlockD.t) (pc: nat) (s: VarSet.t),
      SmartContractD.get_block p fname bid = Some b ->
      live_at_pc' p fname bid pc s ->
      forall v,
        ~ VarSet.In v s ->
        dead_variable p fname bid b pc v.
  Proof.
    unfold dead_variable.
    intros.    
    apply (live_at_snd p n i fname bid b pc s H H0 st1 st1' H2 H3 st2 v H4 H1).
  Qed.

  Theorem live_at_snd_3:   
    forall (p: SmartContractD.t) (fname: FunctionName.t) (bid: BlockID.t) (b: BlockD.t) (s: VarSet.t),
      SmartContractD.get_block p fname bid = Some b ->
      live_in p fname bid s ->
      forall v,
        ~ VarSet.In v s ->
        dead_variable p fname bid b 0 v.
  Proof.
    unfold dead_variable.    
    intros.
    rewrite <- live_at_pc_zero_eq_live_in in H0.
    pose proof (live_at_pc'_equiv_live_at_pc (length (BlockD.instructions b)) p fname bid b s  H (Nat.le_refl (length (BlockD.instructions b)))).
    rewrite Nat.sub_diag in H5.
    rewrite H5 in H0.
    apply (live_at_snd p n i fname bid b 0 s H H0 st1 st1' H2 H3 st2 v H4 H1).
  Qed.
      

  Theorem live_at_snd_4:   
    forall (p: SmartContractD.t) (fname: FunctionName.t) (bid: BlockID.t) (b: BlockD.t) (live_info: sc_live_info_t) (f_live_info: fun_live_info_t) (in_set out_set: VarSet.t),
    SmartContractD.valid_smart_contract p ->
    check_smart_contract p live_info = true ->
    SmartContractD.get_block p fname bid = Some b ->
    live_info fname = Some f_live_info ->
    f_live_info bid = Some (in_set, out_set) ->
    forall v,
      ~ VarSet.In v in_set ->
      dead_variable p fname bid b 0 v.
  Proof.
    intros.
    rewrite <- (check_valid_smart_contract_correct p live_info H) in H0.
    pose proof (snd_info p live_info H0 fname bid b H1).
    destruct H5 as [f_info [b_in_info [b_out_info [H_live_info [H_f_info [H_live_in H_live_out]]]]]].

    rewrite H2 in H_live_info.
    injection H_live_info as H_live_info.
    subst f_info.
    rewrite H3 in H_f_info.
    injection H_f_info as H_in_set _.
    subst in_set.
    
    apply (live_at_snd_3 p fname bid b b_in_info H1 H_live_in v H4).
  Qed.
*)





(*

  (* State rechability in n steps: 'reach_rel_n p n s1 s2' means that from s1 we reach s2 in n execution steps, within the program p *) 
  Inductive reach_rel_n (p : SmartContractD.t) : nat -> StateD.t -> StateD.t -> Prop :=
  | t_step (s1 s2 : StateD.t) :
    SmallStepD.step s1 p = s2 ->  reach_rel_n p 1 s1 s2
  | t_trans (n1 n2: nat) (s1 s2 s3: StateD.t) :
    reach_rel_n p n1 s1 s2 ->
    reach_rel_n p n2 s2 s3 ->
    reach_rel_n p (plus n1 n2) s1 s3.

  (* State rechability: 'reach_rel_n p n s1 s2' means that from s1 we reach s2 in n execution steps, within the program p *) 
  Inductive reach_rel (p : SmartContractD.t) : StateD.t -> StateD.t -> Prop :=
  | reach_n (n : nat) (s1 s2 : StateD.t):
    reach_rel_n p n s1 s2 ->  reach_rel p s1 s2.


 *)
