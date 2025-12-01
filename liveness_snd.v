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
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Pred_Type.


Module Liveness_snd (D: DIALECT).

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

  Lemma some_neq_none {A: Type}:
    forall (x: option A) (y: A),
      x = Some y -> x <> None.
  Proof.
    intros x y H_x.
    congruence.
  Qed.

  
  Lemma forall_not_or_dist : forall (A : Type) (P1 P2 : A -> Prop),
      (forall x, ~(P1 x \/ P2 x)) <-> ((forall x, ~P1 x) /\ (forall x, ~P2 x)).
  Proof.
    intros. split.
    (* Forward direction *)
    - intros H. split; intros x Hx; apply (H x).
      + left. exact Hx.
      + right. exact Hx.
    (* Backward direction *)
    - intros [H1 H2] x [HP1 | HP2].
      + apply (H1 x). exact HP1.
      + apply (H2 x). exact HP2.
  Qed.

  Lemma i_SS_i_p:
    forall i p,
      Nat.lt i (S (S (i + p))).
  Proof.
    intros i p.
    pose proof (Nat.lt_lt_add_r i (S i) p (Nat.lt_succ_diag_r i)) as H_lt_i_aux.
    rewrite plus_Sn_m in H_lt_i_aux.
    apply Nat.lt_lt_succ_r.
    apply H_lt_i_aux.
  Qed.

  Lemma i_SS_i:
    forall i,
      Nat.lt i (S (S i)).
  Proof.
    intros i.
    apply Nat.lt_lt_succ_r.
    apply Nat.lt_succ_diag_r.
  Qed.

  Lemma nat_eq_or_neq:
    forall (x y: nat), x=y \/ x<>y.
  Proof.
    intros x y.
    destruct (Nat.eqb x y) eqn:E_xy.
    - rewrite Nat.eqb_eq in E_xy.
      left.
      apply E_xy.
    - rewrite Nat.eqb_neq in E_xy.
      right.
      apply E_xy.
  Qed.
  
  Lemma list_to_set_spec:
    forall l v,
      List.In v l <-> VarSet.In v (list_to_set l).
  Proof.
    induction l as [|a l' IHl'].
    - intro v.
      simpl.
      split.
      + intros.
        contradiction.
      + intros.
        pose proof (VarSet.empty_spec) as H_empty.
        unfold VarSet.Empty in H_empty.
        contradiction (H_empty v).
    - intro v.
      split.
      + intro H_in_v_al'.
        simpl in H_in_v_al'.
        destruct H_in_v_al' as [H_v_eq_a | H_in_l'].        
        * simpl.
          rewrite VarSet.add_spec.
          left.
          symmetry.
          apply H_v_eq_a.
        * simpl.
          rewrite VarSet.add_spec.
          right.
          apply IHl'.
          apply H_in_l'.
      + intro H_in_v_a_set_l'.
        simpl in H_in_v_a_set_l'.
        rewrite VarSet.add_spec in H_in_v_a_set_l'. 
        destruct H_in_v_a_set_l' as [H_v_eq_a | H_in_set_l'].
        * simpl.
          left.
          symmetry.
          apply H_v_eq_a.
        * simpl.
          right.
          apply IHl'.
          apply H_in_set_l'.
  Qed.

  Lemma extract_yul_vars_spec:
    forall l v,
      List.In (inl v) l <-> List.In v (extract_yul_vars l).
  Proof.
    induction l as [|a l'].
    - intro v.
      split.
      + simpl.
        intros.
        contradiction.
      + simpl.
        intros.
        contradiction.
    - intro v.
      split.
      + intro H_in_inl_v_a_l'.
        simpl in H_in_inl_v_a_l'.
        destruct H_in_inl_v_a_l' as [H_inlv_eq_a | H_in_inl_v_l'].
        * destruct a; try discriminate.
          simpl.
          left.
          injection H_inlv_eq_a as H_inlv_eq_a.
          apply H_inlv_eq_a.
        * destruct a.
          ** simpl.
             right.
             apply IHl'.
             apply H_in_inl_v_l'.
          ** simpl.
             apply IHl'.
             apply H_in_inl_v_l'.
      + intro H_in_v_ex_a_l'.
        destruct a.        
        * simpl in H_in_v_ex_a_l'.
          destruct H_in_v_ex_a_l' as [H_t_eq_v | H_in_v_ex_l'].
          ** simpl.
             left.
             rewrite H_t_eq_v.
             reflexivity.
          ** simpl.
             right.
             apply IHl'.
             apply  H_in_v_ex_l'.
        * simpl in H_in_v_ex_a_l'.
          simpl.
          right.
          apply IHl'.
          apply H_in_v_ex_a_l'.
  Qed.
  
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
      
(*
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

      ++  apply (IHl' (VarSet.remove dest s1) (VarSet.remove dest s2) (remove_preserves_equal s1 s2 dest H_s1_eq_s2)).
  Qed.
 *)

  (*
  Lemma apply_inv_phi_preserves_equal:
    forall l s1 s2,
      VarSet.Equal s1 s2 ->
      VarSet.Equal (apply_inv_phi l s1) (apply_inv_phi l s2).
  Proof.
    induction l as [|a l' IHl'].
    - trivial.
    - intros s1 s2 H_s1_eq_s2.
      unfold apply_inv_phi. fold apply_inv_phi.
      remember (apply_inv_phi l' s1) as s1' eqn:E_s1'.
      remember (apply_inv_phi l' s2) as s2' eqn:E_s2'.
      
      destruct a as [dest orig] eqn:E_do.
      destruct orig as [var|] eqn:E_orig.
      + pose proof (IHl' s1 s2 H_s1_eq_s2) as H_s1'_eq_s2'.
        rewrite <- E_s1' in H_s1'_eq_s2'.
        rewrite <- E_s2' in H_s1'_eq_s2'.

        destruct (VarSet.mem dest s1') eqn:E_mem_dest_s1'; 
          destruct (VarSet.mem dest s2') eqn:E_mem_dest_s2'.

        * apply (add_preserves_equal (VarSet.remove dest s1') (VarSet.remove dest s2') var  (remove_preserves_equal s1' s2' dest H_s1'_eq_s2' ) ).
        * rewrite (mem_preserves_equal s1' s2' dest H_s1'_eq_s2') in E_mem_dest_s1' .
          rewrite E_mem_dest_s1' in E_mem_dest_s2'.
          discriminate E_mem_dest_s2'.

        * rewrite (mem_preserves_equal s1' s2' dest H_s1'_eq_s2') in E_mem_dest_s1' .
          rewrite E_mem_dest_s1' in E_mem_dest_s2'.
          discriminate E_mem_dest_s2'.
        * apply H_s1'_eq_s2'.
      + rewrite E_s1'.
        rewrite E_s2'.
        apply (remove_preserves_equal (apply_inv_phi l' s1) (apply_inv_phi l' s2) dest (IHl' s1 s2 H_s1_eq_s2)).
  Qed.
*)

    
  
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

  Lemma apply_inv_phi_preserves_equal:
    forall l s1 s2,
      VarSet.Equal s1 s2 ->
      VarSet.Equal (apply_inv_phi l s1) (apply_inv_phi l s2).
  Proof.
    intros l s1 s2 H_eq_s1_s2.
    unfold apply_inv_phi.
    remember (list_to_set (SmallStepD.get_renaming_var l)) as outset eqn:E_outset.
    remember (list_to_set (extract_yul_vars (SmallStepD.get_renaming_sexpr l))) as inset eqn:E_inset.

    pose proof (diff_preserves_equal s1 s2 outset outset H_eq_s1_s2 (varset_equal_refl outset)) as H0.

    apply (union_preserves_equal (VarSet.diff s1 outset) (VarSet.diff s2 outset) inset inset H0 (varset_equal_refl inset)).
  Qed.
      

  

  Lemma non_empty_list_cons {A: Type}:
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
  
    
  Lemma live_at_pc'_equiv_live_at_pc:
    forall i p fname bid b s,
      SmartContractD.get_block p fname bid = Some b -> (* the block exists *)
      Nat.le i (length b.(BlockD.instructions)) ->
      live_at_pc p fname bid ((length b.(BlockD.instructions)) - i) s <-> live_at_pc' p fname bid ((length b.(BlockD.instructions)) - i) s.
  Proof.
    Admitted.

  Lemma live_at_pc'_0_equiv_live_at_pc_0:
    forall p fname bid b s,
      SmartContractD.get_block p fname bid = Some b -> (* the block exists *)
      live_at_pc p fname bid 0%nat s <-> live_at_pc' p fname bid 0%nat s.
    Admitted.
  
  Lemma live_at_pc_zero_eq_live_in:
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

  Lemma varlist_in_dec_aux:
    forall l x,
      existsb (fun y => YULVariable.eqb x y) l = false ->
      ~ List.In x l.
  Proof.
    induction l as [|a l'].
    - intros x H_existsb.
      intro. 
      destruct H.
    - intros x H_existsb.
      simpl in H_existsb.
      rewrite orb_false_iff in H_existsb.
      destruct H_existsb as [H_neq_x_a H_existsb_l'].
      simpl.
      intro H_contra.
      destruct H_contra as [H_a_eq_x | H_in_x_l'].
      + unfold YULVariable.eqb in H_neq_x_a.
        symmetry in H_a_eq_x.
        rewrite <- Nat.eqb_eq in H_a_eq_x.
        rewrite H_a_eq_x in H_neq_x_a.
        discriminate H_neq_x_a.
      + pose proof (IHl' x H_existsb_l') as IHl'_inst.
        contradiction.
  Qed.

  Lemma varlist_in_dec:
    forall (l: list YULVariable.t) (x: YULVariable.t),
      List.In x l \/ ~ List.In x l.
  Proof.
    intros l x.
    destruct (existsb (fun y => YULVariable.eqb x y) l) eqn:E_exists.
    - rewrite existsb_exists in E_exists.
      destruct E_exists as [x0 [H_in_x0_l H_x0_eqb_x]].
      unfold YULVariable.eqb in H_x0_eqb_x.
      rewrite Nat.eqb_eq in H_x0_eqb_x.
      left.
      rewrite H_x0_eqb_x.
      apply H_in_x0_l.
    - right.
      apply (varlist_in_dec_aux l x E_exists).
  Qed.

    Lemma varmap_in_dec_aux:
    forall (l: YULVariableMapD.t) (x: YULVariable.t),
      existsb (fun y => YULVariable.eqb x (fst y)) l = false ->
      ~ exists sexpr, List.In (x,sexpr) l.
  Proof.
    induction l as [|a l'].
    - intros x H_existsb.
      intro. 
      destruct H as [sexpr H].
      destruct H.
    - intros x H_existsb.
      destruct a as [dest orig].
      simpl in H_existsb.
      rewrite orb_false_iff in H_existsb.
      destruct H_existsb as [H_neq_x_a H_existsb_l'].
      simpl.
      intro H_contra.
      destruct H_contra as [sexpr [H_a_eq_x | H_in_x_l']].
      + unfold YULVariable.eqb in H_neq_x_a.
        symmetry in H_a_eq_x.
        injection H_a_eq_x as H_x H_dest.
        rewrite Nat.eqb_neq in H_neq_x_a.
        contradiction.
      + apply (IHl' x H_existsb_l').
        exists sexpr.
        apply H_in_x_l'.
  Qed.

  Lemma varmap_in_dec:
    forall (l: YULVariableMapD.t) (x: YULVariable.t),
      (exists sexpr, List.In (x,sexpr) l) \/ (~ exists sexpr, List.In (x,sexpr) l).
  Proof.
    intros l x.
    destruct (existsb (fun y => YULVariable.eqb x (fst y)) l) eqn:E_exists.
    - rewrite existsb_exists in E_exists.      
      destruct E_exists as [ [xvar sexpr] [H_in_x0_l H_x0_eqb_x]].
      unfold YULVariable.eqb in H_x0_eqb_x.
      simpl in H_x0_eqb_x.
      rewrite Nat.eqb_eq in H_x0_eqb_x.
      left.
      exists sexpr.
      rewrite H_x0_eqb_x.
      apply H_in_x0_l.
    - right.
      apply (varmap_in_dec_aux l x E_exists).
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

  Lemma not_In_cons_ {A: Type}:
    forall (l: list A) (b: A),
      (forall a, ~ In a (b::l)) ->
      (forall a, ~ In a l).
  Proof.
    intros l b H_not_in.
    simpl in H_not_in.
    intro a.
    intro H_contra.
    pose proof (H_not_in a) as H.
    apply Decidable.not_or in H.
    destruct H as [_ H].
    contradiction.
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
    
  Lemma eval_sexpr_snd:
    forall l fname bid pc v sf1 sf2,
      equiv_stack_frames_up_to_v fname bid pc v sf1 sf2 ->
      ~List.In (inl v) l ->
      SmallStepD.eval_sexpr l sf1 = 
        SmallStepD.eval_sexpr l sf2.
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
        (*{*)
          intro H_contra.
          apply H_v_neq_var_inl.
          rewrite H_contra.
          reflexivity.
        (*}.*)
        destruct H_eq_sf1_sf2 as [_ [_ [_ [_ [_ [_ H_eq_sf1_sf2]]]]]].
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
    (*{*)
      intros H_contra.
      rewrite H_contra in H_get_next.
      discriminate H_get_next.
    (*}.*)
    
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

  Lemma equiv_states_eq_dialect:
    forall p i fname bid pc v st1 st2,
      equiv_states_up_to_i_v p i fname bid pc v st1 st2 ->
      st1.(StateD.dialect_state) = st2.(StateD.dialect_state).
  Proof.
    intros p i fname bid pc v st1 st2 H_equiv_st1_st2.
    apply H_equiv_st1_st2.
  Qed.

  Lemma equiv_states_non_nil_call_stack:
    forall p i fname bid pc v st1 st2,
      equiv_states_up_to_i_v p i fname bid pc v st1 st2 ->
      st1.(StateD.call_stack) <> [] /\ st2.(StateD.call_stack) <> [].
  Proof.
    intros p i fname bid pc v st1 st2 H_equiv_st1_st2.
    unfold equiv_states_up_to_i_v in H_equiv_st1_st2.
    destruct H_equiv_st1_st2 as [_ [_ [_ [_ [hl [tl [sf1 [sf2 [H_split_i_st1 [H_split_i_st2 H_equiv_frame]]]]]]]]]].
    unfold split_at_i in H_split_i_st1.
    destruct H_split_i_st1 as [_ [H_call_stack_st1 _]].
    unfold split_at_i in H_split_i_st2.
    destruct H_split_i_st2 as [_ [H_call_stack_st2 _]].
    destruct hl as [|sftop hl'].
    - simpl in H_call_stack_st1. simpl in H_call_stack_st2.
      split.
      + intros H_contra.
        rewrite H_contra in H_call_stack_st1.
        discriminate H_call_stack_st1.
      + intros H_contra.
        rewrite H_contra in H_call_stack_st2.
        discriminate H_call_stack_st2.
    - simpl in H_call_stack_st1. simpl in H_call_stack_st2.
      split.
      + intros H_contra.
        rewrite H_contra in H_call_stack_st1.
        discriminate H_call_stack_st1.
      + intros H_contra.
        rewrite H_contra in H_call_stack_st2.
        discriminate H_call_stack_st2.
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
      destruct H_equiv_frame_up_to_v_sf1_sf2 as [H_fname_sf1 [H_bid_sf1 [H_sf1_pc [H_fname_sf2 [H_bid_sf2 [H_pc_sf2 H_eq_assgin_up_to_v]]]]]].
      subst fname.
      subst bid.
      subst pc.

      repeat split.
      + apply (symmetry H_fname_sf2).
      + apply (symmetry H_bid_sf2).
      + apply (symmetry H_pc_sf2).
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

  Lemma set_status_preserves_call_stack:
    forall st status,
      st.(StateD.call_stack) = (SmallStepD.StateD.set_status st status).(StateD.call_stack).
  Proof.
    destruct st.
    reflexivity.
  Qed.

  Lemma set_status_preserves_dialect_state:
    forall st status,
      st.(StateD.dialect_state) = (SmallStepD.StateD.set_status st status).(StateD.dialect_state).
  Proof.
    destruct st.
    reflexivity.
  Qed.


  Lemma accessed_var_instr_neq_v:
    forall p fname bid b pc s0 v0 s v,
      SmartContractD.get_block p fname bid = Some b ->
      live_at_pc' p fname bid pc s ->
      ~ VarSet.In v s ->
      accessed_vars b pc s0 ->
      VarSet.In v0 s0 ->
      v0 <> v.
  Proof.
    intros p fname bid b pc s0 v0 s v H_b_exists H_live_at_pc H_not_In_v_s H_accessed_vars H_In_v0_s0.
    destruct H_live_at_pc as [fname bid b0 pc s sout H_b0_exists H_live_out H_pc_at_end H_sout | fname bid b0 pc s sout instr H_b0_exists H_live_at_S_pc H_lt_pc' H_get_instr H_sout].
    - rewrite H_b_exists in H_b0_exists.
      injection H_b0_exists as H_b0_exists.
      subst b0.
      unfold accessed_vars in H_accessed_vars.
      destruct H_accessed_vars as [H_pc_eq_len | H_pc_lt_len].

      + destruct H_pc_eq_len as [H_pc_eq_len H_match]. 
        destruct (BlockD.exit_info b) as [cv | | rvs | ] eqn:E_exit_b.
        * unfold add_jump_var_if_applicable in H_sout.
          rewrite E_exit_b in H_sout.
          pose proof (not_In_preserves_eq sout (VarSet.add cv s) v H_sout H_not_In_v_s) as H_not_In_v_add.
          pose proof (In_preserves_eq s0 (VarSet.add cv VarSet.empty) v0 H_match H_In_v0_s0) as H_In_v0_add.
          rewrite VarSet.add_spec in H_not_In_v_add.
          rewrite VarSet.add_spec in H_In_v0_add.
          apply Decidable.not_or in H_not_In_v_add.
          destruct H_not_In_v_add as [H_v_neq_cv H_not_In_v_s'].
          destruct H_In_v0_add as [H_eq_v0_cv | H_In_v0_empty].
          ** rewrite H_eq_v0_cv.
             apply not_eq_sym.
             apply H_v_neq_cv.
          ** pose proof (VarSet.empty_spec) as H_empty.
             unfold VarSet.Empty in H_empty.
             contradiction (H_empty v0).
        * unfold add_jump_var_if_applicable in H_sout.
          rewrite E_exit_b in H_sout.      
          pose proof (In_preserves_eq s0 VarSet.empty v0 H_match H_In_v0_s0 ) as H_In_v0_empty.
          pose proof (VarSet.empty_spec) as H_empty.
          unfold VarSet.Empty in H_empty.
          contradiction (H_empty v0).

        * unfold add_jump_var_if_applicable in H_sout.
          rewrite E_exit_b in H_sout.

          destruct H_live_out as [ fname bid b0 rs sout0 H_b0_exists H_is_ret H_sout0| fname bid b0 sout0 H_b0_exists H_is_termin | fname bid next_bid b0 next_b0 s' sout0 H_b0_exists H_is_jump | fname bid  next_bid_if_true next_bid_if_false cvar b0 next_b0_if_true next_b0_if_false s1' s2' sout0 H_b0_exists H_is_cjump ].
          ** rewrite H_b_exists in H_b0_exists.
             injection H_b0_exists as H_b0_exists.
             subst b0.
             unfold BlockD.is_return_block in H_is_ret.
             rewrite  E_exit_b in H_is_ret.
             injection  H_is_ret as  H_is_ret.
             subst rs.
             rewrite H_sout0  in H_sout.
             
             pose proof (not_In_preserves_eq sout (list_to_set (extract_yul_vars rvs)) v H_sout H_not_In_v_s) as H_not_in_v_rets.
             pose proof (In_preserves_eq  s0 (list_to_set (extract_yul_vars rvs)) v0 H_match H_In_v0_s0) as H_in_v0_rets.
             apply (not_In_neq v0 v (list_to_set (extract_yul_vars rvs)) H_in_v0_rets H_not_in_v_rets).

          ** rewrite H_b_exists in H_b0_exists.
             injection H_b0_exists as H_b0_exists.
             subst b0.
             unfold BlockD.is_terminated_block in H_is_termin.
             rewrite  E_exit_b in H_is_termin.
             discriminate H_is_termin.

          ** rewrite H_b_exists in H_b0_exists.
             injection H_b0_exists as H_b0_exists.
             subst b0.
             unfold BlockD.is_jump_block in H_is_jump.
             rewrite E_exit_b in H_is_jump.
             discriminate H_is_jump.

          ** rewrite H_b_exists in H_b0_exists.
             injection H_b0_exists as H_b0_exists.
             subst b0.
             unfold BlockD.is_cond_jump_block in H_is_cjump.
             rewrite E_exit_b in H_is_cjump.
             discriminate H_is_cjump.
        * pose proof (In_preserves_eq  s0 VarSet.empty v0 H_match H_In_v0_s0) as H_In_v0_empty.  
          pose proof (VarSet.empty_spec) as H_empty.
          unfold VarSet.Empty in H_empty.
          contradiction (H_empty v0).
          
      + destruct H_pc_lt_len as [H_pc_lt_len _].
        rewrite H_pc_at_end in H_pc_lt_len.
        contradiction (Nat.lt_irrefl (length (BlockD.instructions b))).
    - rewrite H_b_exists in H_b0_exists.
      injection H_b0_exists as H_b0_exists.
      subst b0.
      unfold accessed_vars in H_accessed_vars.
      destruct H_accessed_vars as [H_pc_eq_len | H_pc_lt_len].

      + destruct H_pc_eq_len as [H_pc_eq_len _].
        rewrite H_pc_eq_len in H_lt_pc'.
        contradiction (Nat.lt_irrefl (length (BlockD.instructions b))).

      + destruct H_pc_lt_len as [_ [instr' [H_nth_err H_s0]]].
        rewrite H_get_instr in H_nth_err.
        injection H_nth_err as H_nth_err.
        subst instr'.
        unfold prop_live_set_bkw_instr in H_sout.
        pose proof (not_In_preserves_eq sout (VarSet.union (VarSet.diff s (list_to_set (InstructionD.output instr))) (list_to_set (extract_yul_vars (InstructionD.input instr)))) v H_sout H_not_In_v_s) as H_not_In_v_union.
        rewrite VarSet.union_spec in H_not_In_v_union.
        apply Decidable.not_or in H_not_In_v_union.
        destruct H_not_In_v_union as [_ H_not_in_args].
        pose proof (In_preserves_eq s0 (list_to_set (extract_yul_vars (InstructionD.input instr))) v0 H_s0 H_In_v0_s0 ) as H_in_v0_args.
        pose proof (not_In_neq v0 v (list_to_set (extract_yul_vars (InstructionD.input instr))) H_in_v0_args H_not_in_args) as H_neq_v0_v.
        intro H_contra.
        contradiction.
  Qed.
    
  Lemma assign_all_succ:
    forall l vs assign,
      length l = length vs ->
      exists new_assign,        
        SmallStepD.VariableAssignmentD.assign_all assign l vs = Some new_assign.
  Proof.
    induction l as [|a l'].
    - intros vs assign H_len.
      destruct vs; try discriminate.
      exists assign.
      simpl.
      reflexivity.
    - intros vs assign H_len.
      destruct vs as [|v vs']; try discriminate.
      simpl in H_len.
      simpl.
      apply (IHl' vs' (SmallStepD.VariableAssignmentD.assign assign a v) (eq_add_S (length l') (length vs') H_len)).
  Qed.

  Lemma assign_preserves_equiv_up_to_v:
    forall assign1 assign2 v a val, 
      (forall v' : YULVariable.t,
          v' <> v -> VariableAssignmentD.get assign1 v' = VariableAssignmentD.get assign2 v') ->
      (forall v' : YULVariable.t,
          v' <> v -> VariableAssignmentD.get (SmallStepD.VariableAssignmentD.assign assign1 a val) v' = VariableAssignmentD.get (SmallStepD.VariableAssignmentD.assign assign2 a val) v').
  Proof.
    intros assign1 assign2 v a val H.
    intros v' H_neq_v'_v.
    unfold SmallStepD.VariableAssignmentD.assign.
    unfold SmallStepD.VariableAssignmentD.get.
    destruct (YULVariable.eqb v' a); try reflexivity.
    apply (H v' H_neq_v'_v).
  Qed.
       
        
  Lemma assign_all_preserves_eq_up_to:
    forall l assign1 assign2 v vs new_assign1 new_assign2,
      ~ List.In v l ->
      (forall v' : YULVariable.t,
          v' <> v -> VariableAssignmentD.get assign1 v' = VariableAssignmentD.get assign2 v') ->
      SmallStepD.VariableAssignmentD.assign_all assign1 l vs = Some new_assign1 ->
      SmallStepD.VariableAssignmentD.assign_all assign2 l vs = Some new_assign2 ->
      (forall v' : YULVariable.t,
          v' <> v -> VariableAssignmentD.get new_assign1 v' = VariableAssignmentD.get new_assign2 v').
  Proof. 
    induction l as [| a l'].

    - simpl.
      intros assign1 assign2 v vs new_assign1 new_assign2 H_In_v_l H_equiv H_assign1_all H_assign2_all.
      destruct vs; try discriminate.
      injection H_assign1_all as H_assign1_all.
      injection H_assign2_all as H_assign2_all.
      rewrite <- H_assign1_all.
      rewrite <- H_assign2_all.
      apply H_equiv.

    - intros assign1 assign2 v vs new_assign1 new_assign2 H_In_v_l H_equiv H_assign1_all H_assign2_all.
 
      destruct vs as [| v' vs']; try discriminate.
      simpl in H_assign1_all.
      simpl in H_assign2_all.

      simpl in H_In_v_l.
      apply Decidable.not_or in H_In_v_l.
      destruct H_In_v_l as [H_v_neq_a H_In_v_l'].
      
      pose proof (assign_preserves_equiv_up_to_v assign1 assign2 v a v' H_equiv) as H_equiv_ext. 

      apply (IHl' (SmallStepD.VariableAssignmentD.assign assign1 a v') (SmallStepD.VariableAssignmentD.assign assign2 a v') v vs' new_assign1 new_assign2 H_In_v_l' H_equiv_ext H_assign1_all H_assign2_all).
  Qed.      

    Lemma assign_preserves_eq_up_to_equiv_v:
    forall assign1 assign2 v value,
      (forall v' : YULVariable.t,
          v' <> v -> VariableAssignmentD.get assign1 v' = VariableAssignmentD.get assign2 v') ->
      (forall v' : YULVariable.t,
          VariableAssignmentD.get (SmallStepD.VariableAssignmentD.assign assign1 v value) v' = VariableAssignmentD.get (SmallStepD.VariableAssignmentD.assign assign2 v value) v').
    Proof.
      intros assign1 assign2 v value H_equiv_up_to_v.
      intros v'.
      unfold SmallStepD.VariableAssignmentD.assign.
      unfold VariableAssignmentD.get.
      destruct (YULVariable.eqb v' v) eqn:E_v'_eqb_v; try reflexivity.
      unfold YULVariable.eqb in E_v'_eqb_v.
      rewrite Nat.eqb_neq in E_v'_eqb_v.
      apply (H_equiv_up_to_v v' E_v'_eqb_v).
    Qed.

    Lemma assign_preserves_eq_up_to_equiv_any:
    forall assign1 assign2 v a value,
      (forall v' : YULVariable.t,
          v' <> v -> VariableAssignmentD.get assign1 v' = VariableAssignmentD.get assign2 v') ->
      (forall v' : YULVariable.t,
          v' <> v -> VariableAssignmentD.get (SmallStepD.VariableAssignmentD.assign assign1 a value) v' = VariableAssignmentD.get (SmallStepD.VariableAssignmentD.assign assign2 a value) v').
    Proof.
      intros assign1 assign2 v a value H_equiv_up_to_v.
      intros v'.
      intro H_neq_v'_v.
      unfold SmallStepD.VariableAssignmentD.assign.
      unfold VariableAssignmentD.get.
      destruct (YULVariable.eqb v' a).
      - reflexivity.
      - apply (H_equiv_up_to_v v' H_neq_v'_v).
    Qed.

    Lemma assign_preserves_eq_up_to_eq:
    forall assign1 assign2 v value,
      (forall v' : YULVariable.t,
          v' <> v -> VariableAssignmentD.get assign1 v' = VariableAssignmentD.get assign2 v') ->
      SmallStepD.VariableAssignmentD.assign assign1 v value = SmallStepD.VariableAssignmentD.assign assign2 v value.
    Proof.
      intros assign1 assign2 v value H_equiv_up_to_v.
      pose proof (assign_preserves_eq_up_to_equiv_v assign1 assign2 v value H_equiv_up_to_v) as H_equiv.
      unfold VariableAssignmentD.get in H_equiv.
      apply functional_extensionality in H_equiv.
      apply H_equiv.
    Qed.

    Lemma assign_all_preserves_eq_up_to_equiv:
    forall l assign1 assign2 v vs new_assign1 new_assign2,
      List.In v l ->
      (forall v' : YULVariable.t,
          v' <> v -> VariableAssignmentD.get assign1 v' = VariableAssignmentD.get assign2 v') ->
      SmallStepD.VariableAssignmentD.assign_all assign1 l vs = Some new_assign1 ->
      SmallStepD.VariableAssignmentD.assign_all assign2 l vs = Some new_assign2 ->
      (forall v' : YULVariable.t,
          VariableAssignmentD.get new_assign1 v' = VariableAssignmentD.get new_assign2 v').
    Proof.
      induction l as [|a l' IHl'].
      - intros assign1 assign2 v vs new_assign1 new_assign2 H_In_v_l.
        contradiction (in_nil H_In_v_l).
      - intros assign1 assign2 v vs new_assign1 new_assign2 H_In_v_l.
        intros H_equiv_up_to_v H_assign_all_1 H_assign_all_2.
        simpl in H_assign_all_1.
        simpl in H_assign_all_2.
        destruct vs as [|v' vs']; try discriminate.
        pose proof (assign_preserves_eq_up_to_eq assign1 assign2 v v' H_equiv_up_to_v) as H_assign_equiv.

        pose proof (nat_eq_or_neq a v) as H_a_v.
        destruct H_a_v as [H_eq_a_v | H_neq_a_v].

        + rewrite H_eq_a_v in H_assign_all_1.
          rewrite H_eq_a_v in H_assign_all_2.
          rewrite H_assign_equiv in H_assign_all_1.
          rewrite H_assign_all_1 in H_assign_all_2.
          injection H_assign_all_2 as H_assign_all_2.
          rewrite H_assign_all_2.
          reflexivity.
        + pose proof (assign_preserves_eq_up_to_equiv_any assign1 assign2 v a v' H_equiv_up_to_v) as H_equiv_up_to_v_a.

          simpl in H_In_v_l.
          destruct H_In_v_l as [H_a_eq_v | H_In_v_l'].
          * contradiction.
          * apply (IHl' (SmallStepD.VariableAssignmentD.assign assign1 a v') (SmallStepD.VariableAssignmentD.assign assign2 a v') v vs' new_assign1 new_assign2 H_In_v_l' H_equiv_up_to_v_a H_assign_all_1 H_assign_all_2).
    Qed.
          
    Lemma assign_all_preserves_eq_up_to_eq:
    forall l assign1 assign2 v vs new_assign1 new_assign2,
      List.In v l ->
      (forall v' : YULVariable.t,
          v' <> v -> VariableAssignmentD.get assign1 v' = VariableAssignmentD.get assign2 v') ->
      SmallStepD.VariableAssignmentD.assign_all assign1 l vs = Some new_assign1 ->
      SmallStepD.VariableAssignmentD.assign_all assign2 l vs = Some new_assign2 ->
      new_assign1 = new_assign2.
    Proof.
      intros l assign1 assign2 v vs new_assign1 new_assign2 H_In_v_l H_equiv H_assign_1 H_assign_2.
      pose proof (assign_all_preserves_eq_up_to_equiv l assign1 assign2 v vs new_assign1 new_assign2 H_In_v_l H_equiv H_assign_1 H_assign_2) as H_equiv'.
      unfold VariableAssignmentD.get in H_equiv'.
      apply functional_extensionality in H_equiv'.
      apply H_equiv'.
    Qed.


    Lemma not_In_v_fwd:
      forall v s sout instr,
        VarSet.Equal sout (prop_live_set_bkw_instr instr s) ->
        ~ VarSet.In v sout ->
        ~ List.In v instr.(InstructionD.output) ->
        ~ VarSet.In v s.
    Proof.
      intros v s sout instr H_eq_sout H_not_In_v_sout H_not_in_v_output.
      unfold prop_live_set_bkw_instr in H_eq_sout.
      pose proof (not_In_preserves_eq sout (VarSet.union (VarSet.diff s (list_to_set (InstructionD.output instr))) (list_to_set (extract_yul_vars (InstructionD.input instr)))) v H_eq_sout H_not_In_v_sout) as H_not_In_v_union.
      rewrite VarSet.union_spec in H_not_In_v_union.
      apply Decidable.not_or in H_not_In_v_union.
      destruct H_not_In_v_union as [H_not_In_v_diff _].
      rewrite VarSet.diff_spec in H_not_In_v_diff.

      apply Decidable.not_and in H_not_In_v_diff.
      - destruct H_not_In_v_diff as [H | H].
        + apply H.
        + apply Decidable.not_not in H.
          * rewrite <- list_to_set_spec in H.
            contradiction.
          * apply varset_in_dec.
      - apply varset_in_dec.
    Qed.

  Lemma assign_all_some:   
    forall l vs assign1 assign2 assign1',
      SmallStepD.CallStackD.StackFrameD.VariableAssignmentD.assign_all assign1 l vs = Some assign1'
    ->
      (exists assign2', SmallStepD.CallStackD.StackFrameD.VariableAssignmentD.assign_all assign2 l vs = Some assign2').
  Proof.
    induction l as [|a l' IHl'].
    - intros vs assign1 assign2 assign1'.
      destruct vs as [|v vs'].
      + simpl.
        intros.
        exists assign2.
        reflexivity.
      + intros H.
        simpl in H.
        discriminate H.
    - intros vs assign1 assign2 assign1' H.
      simpl in H.
      simpl.
      destruct vs as [|v vs'].
      + discriminate H.
      + apply (IHl' vs' (SmallStepD.CallStackD.StackFrameD.VariableAssignmentD.assign assign1 a v) (SmallStepD.CallStackD.StackFrameD.VariableAssignmentD.assign assign2 a v) assign1' H).
  Qed.

  Lemma assign_all_none:   
    forall l vs assign1 assign2,
      SmallStepD.CallStackD.StackFrameD.VariableAssignmentD.assign_all assign1 l vs = None
    ->
     SmallStepD.CallStackD.StackFrameD.VariableAssignmentD.assign_all assign2 l vs = None.
  Proof.
    intros.
    destruct (SmallStepD.CallStackD.StackFrameD.VariableAssignmentD.assign_all assign2 l vs) as [assign2'|] eqn:E; try reflexivity.
    pose proof (assign_all_some l vs assign2 assign1 assign2' E) as H0.
    destruct H0 as [assign1' H0].
    rewrite H0 in H.
    discriminate H.
  Qed.
  
      
      

  Lemma live_at_exec_inst_snd:   
    forall (p: SmartContractD.t) (i: nat) (fname: FunctionName.t) (bid: BlockID.t) (b: BlockD.t) (pc: nat) (s: VarSet.t) (instr: InstructionD.t),
      SmartContractD.get_block p fname bid = Some b ->
      live_at_pc' p fname bid pc s ->
      forall  (st1 st2 st1': StateD.t) (v: YULVariable.t),
        equiv_states_up_to_i_v p i fname bid pc v st1 st2 ->
        SmallStepD.get_next_instruction st1 p = Some instr ->
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
    intros p i fname bid b pc s instr H_b_exists H_live_at_pc st1 st2 st1' v H_equiv_st1_st2 H_get_instr H_exec_inst_st1 H_not_In_v_s.

    assert (H_equiv_st1_st2' := H_equiv_st1_st2).
    unfold equiv_states_up_to_i_v in H_equiv_st1_st2'.
    destruct H_equiv_st1_st2' as [H_lt_i [H_len_call_stack [H_status [H_dialect [hl [tl [sf1 [sf2 [H_split_i_st1 [H_split_i_st2 H_equiv_sf1_sf2]]]]]]]]]].

    unfold split_at_i in H_split_i_st1.
    destruct H_split_i_st1 as [H_lt_i_st1 [H_call_stack_st1 H_len_tl_st1]].
    
    unfold split_at_i in H_split_i_st2.
    destruct H_split_i_st2 as [H_lt_i_st2 [H_call_stack_st2 H_len_tl_st2]].
    
    
    destruct hl as [|top_sf hl'] eqn:E_hl.

    (* the case where the top stack frame is the one with different values for v *)
    + simpl in H_call_stack_st1.
      simpl in H_call_stack_st2.

      assert(H_sf1_name: (StackFrameD.function_name sf1) = fname). apply H_equiv_sf1_sf2.
      assert(H_sf1_bid: (StackFrameD.curr_block_id sf1) = bid). apply H_equiv_sf1_sf2.
      assert(H_sf1_pc: (StackFrameD.pc sf1) = pc). apply H_equiv_sf1_sf2.

      assert(H_b_exists' := H_b_exists).
      rewrite <- H_sf1_name in H_b_exists'.
      rewrite <- H_sf1_bid in H_b_exists'.
      
      pose proof (get_next_instruction_succ st1 p instr sf1 tl b H_call_stack_st1 H_b_exists' H_get_instr) as H_pc_is_not_at_end.
      assert(H_live_at_pc' := H_live_at_pc).
      destruct H_live_at_pc' as [fname bid b0 pc s sout H_b0_exists _ H_pc_at_end | fname bid b0 pc s sout instr' H_b0_exists H_live_at_S_pc H_lt_pc H_get_instr' H_sout].

      (* this case is not applicable since pc is not at the end *)
      * rewrite H_b_exists in H_b0_exists.
        injection H_b0_exists as H_b0_exists.
        subst b0.
        rewrite H_sf1_pc in H_pc_is_not_at_end.
        rewrite H_pc_at_end in H_pc_is_not_at_end.
        contradiction (Nat.lt_irrefl (length (BlockD.instructions b))).
      * rewrite H_b_exists in H_b0_exists.
        injection H_b0_exists as H_b0_exists.
        subst b0.

        (* eliminate instr' *)
        assert(H_get_instr'' := H_get_instr).
        unfold SmallStepD.get_next_instruction in H_get_instr''.
        rewrite H_call_stack_st1 in H_get_instr''.
        rewrite H_sf1_name in H_get_instr''.
        rewrite H_sf1_bid in H_get_instr''.
        rewrite H_sf1_pc in H_get_instr''.
        unfold SmallStepD.SmartContractD.get_instruction in H_get_instr''.
        rewrite H_b_exists in H_get_instr''.
        rewrite H_get_instr'' in H_get_instr'.
        injection H_get_instr' as H_get_instr'.
        subst instr'.

        destruct instr as  [input output op] eqn:E_instr.

        assert (H_not_In_v_input: ~ In (inl v) instr.(InstructionD.input)).
        {
          unfold prop_live_set_bkw_instr in H_sout.
          pose proof (not_In_preserves_eq
                        sout
                        (VarSet.union
                           (VarSet.diff s
                              (list_to_set
                                 (InstructionD.output
                                    {|
                                      Liveness_snd.InstructionD.input := input;
                                      Liveness_snd.InstructionD.output := output;
                                      Liveness_snd.InstructionD.op := op
                                    |})))
                           (list_to_set
                              (extract_yul_vars
                                 (InstructionD.input
                                    {|
                                      Liveness_snd.InstructionD.input := input;
                                      Liveness_snd.InstructionD.output := output;
                                      Liveness_snd.InstructionD.op := op
                                    |}))))
                        v H_sout H_not_In_v_s) as H_not_In_v_union.
          rewrite VarSet.union_spec in H_not_In_v_union.
          apply Decidable.not_or in H_not_In_v_union.
          destruct H_not_In_v_union as [_ H_not_In_v_union].
          rewrite <- list_to_set_spec in H_not_In_v_union.
          rewrite <- extract_yul_vars_spec in H_not_In_v_union.
          rewrite E_instr.
          apply H_not_In_v_union.
        }.
        
        pose proof (eval_sexpr_snd (instr.(InstructionD.input)) fname bid pc v sf1 sf2 H_equiv_sf1_sf2 H_not_In_v_input) as H_eval_sf1_eq_eval_sf2.

        rewrite <- E_instr in H_exec_inst_st1.
        unfold SmallStepD.execute_instr in H_exec_inst_st1.
        rewrite H_call_stack_st1 in H_exec_inst_st1.

        rewrite <- E_instr.
        unfold SmallStepD.execute_instr.
        rewrite H_call_stack_st2.

        rewrite <- H_eval_sf1_eq_eval_sf2.

        assert(H_equiv_sf1_sf2' := H_equiv_sf1_sf2).
        unfold equiv_stack_frames_up_to_v in H_equiv_sf1_sf2'.
        destruct H_equiv_sf1_sf2' as [H_fname_sf1 [H_bid_sf1 [H_pc_sf1 [H_fname_sf2 [H_bid_sf2 [H_pc_sf2 H_equiv_assign_sf1_sf2]]]]]].
        
        (* consider the different cases of operators *)
        destruct (SmallStepD.SmartContractD.BlockD.InstructionD.op instr) as [ f_or_op | assignment ] eqn:E_op; try destruct f_or_op as [f_call | op_call].

        (* function call *)
        ** destruct (SmallStepD.SmartContractD.get_function p f_call) eqn:E_f_call.

           *** destruct (SmallStepD.CallStackD.StackFrameD.VariableAssignmentD.assign_all SmallStepD.CallStackD.StackFrameD.VariableAssignmentD.empty (SmallStepD.SmartContractD.FunctionD.arguments t) (SmallStepD.eval_sexpr (SmallStepD.SmartContractD.BlockD.InstructionD.input instr) sf1)).

               **** remember {|
                        Liveness_snd.StateD.call_stack :=
                          {|
                            Liveness_snd.StackFrameD.function_name := f_call;
                            Liveness_snd.StackFrameD.variable_assignments := t0;
                            Liveness_snd.StackFrameD.curr_block_id :=
                              SmallStepD.SmartContractD.FunctionD.entry_block_id t;
                            Liveness_snd.StackFrameD.pc := 0;
                          |} :: sf2 :: tl;
                        Liveness_snd.StateD.status := SmallStepD.StateD.status st2;
                        Liveness_snd.StateD.dialect_state := SmallStepD.StateD.dialect_state st2
                      |} as st2' eqn:H_st2'.
                    exists st2'.
                    exists bid.
                    exists b.
                    exists pc.
                    exists sout.
                    repeat split.
                    ***** apply H_b_exists.
                    ***** left.
                          repeat split.
                          ****** rewrite <- H_exec_inst_st1.
                                 simpl.
                                 rewrite H_call_stack_st1 in H_lt_i_st1.
                                 simpl in H_lt_i_st1.
                                 apply Nat.lt_lt_succ_r.
                                 apply H_lt_i_st1.
                          ****** rewrite <- H_exec_inst_st1.
                                 rewrite H_st2'.
                                 simpl.
                                 reflexivity.
                          ****** rewrite <- H_exec_inst_st1.
                                 rewrite H_st2'.
                                 simpl.
                                 apply H_status.
                          ****** rewrite <- H_exec_inst_st1.
                                 rewrite H_st2'.
                                 simpl.
                                 apply H_dialect.
                          ****** exists [{|
                                       Liveness_snd.StackFrameD.function_name := f_call;
                                       Liveness_snd.StackFrameD.variable_assignments := t0;
                                       Liveness_snd.StackFrameD.curr_block_id :=
                                         SmallStepD.SmartContractD.FunctionD.entry_block_id t;
                                       Liveness_snd.StackFrameD.pc := 0
                                     |}].
                                 exists tl.
                                 exists sf1.
                                 exists sf2.
                                 repeat split.
                                 ******* rewrite <- H_exec_inst_st1.
                                         simpl.
                                         rewrite H_call_stack_st1 in H_lt_i_st1.
                                         simpl in H_lt_i_st1.
                                         apply (Nat.lt_trans i (S (length tl)) (S (S (length tl))) H_lt_i_st1 (Nat.lt_succ_diag_r (S (length tl)) )).
                                 ******* rewrite <- H_exec_inst_st1.
                                         simpl.
                                         reflexivity.
                                 ******* apply H_len_tl_st2.
                                 ******* rewrite H_st2'.
                                         simpl.
                                         rewrite H_call_stack_st1 in H_lt_i_st1.
                                         simpl in H_lt_i_st1.
                                         apply (Nat.lt_trans i (S (length tl)) (S (S (length tl))) H_lt_i_st1 (Nat.lt_succ_diag_r (S (length tl)) )).
                                 ******* rewrite H_st2'.
                                         simpl.
                                         reflexivity.
                                 ******* apply H_len_tl_st2.
                                 ******* apply H_equiv_sf1_sf2.
                                 ******* apply H_equiv_sf1_sf2.
                                 ******* apply H_equiv_sf1_sf2.
                                 ******* apply H_equiv_sf1_sf2.
                                 ******* apply H_equiv_sf1_sf2.
                                 ******* apply H_equiv_sf1_sf2.
                                 ******* apply H_equiv_sf1_sf2.
                          ****** apply H_live_at_pc.
                          ****** apply H_not_In_v_s.
                    ***** rewrite <- H_exec_inst_st1.
                          rewrite H_st2'.
                          unfold equiv_vars_in_top_frame.
                          simpl.
                          repeat split; reflexivity.
               **** remember (SmallStepD.StateD.set_status st2 (Status.Error "Failed to create initial variable assignment")) as st2' eqn:H_st2'.
                    exists st2'.
                    exists bid.
                    exists b.
                    exists pc.
                    exists sout.
                    repeat split.
                    ***** apply H_b_exists.
                    ***** left.
                          repeat split.
                          ****** rewrite <- H_exec_inst_st1.
                                 simpl.
                                 apply H_lt_i_st1.
                          ****** rewrite <- H_exec_inst_st1.
                                 rewrite H_st2'.
                                 simpl.
                                 apply H_len_call_stack.
                          ****** rewrite <- H_exec_inst_st1.
                                 rewrite H_st2'.
                                 simpl.   
                                 reflexivity.
                          ****** rewrite <- H_exec_inst_st1.
                                 rewrite H_st2'.
                                 simpl.   
                                 apply H_dialect.
                          ****** exists [].
                                 exists tl.
                                 exists sf1.
                                 exists sf2.
                                 repeat split.
                                 ******* rewrite <- H_exec_inst_st1.
                                         simpl.
                                         apply H_lt_i_st1.
                                 ******* rewrite <- H_exec_inst_st1.
                                         simpl.
                                         apply H_call_stack_st1.
                                 ******* apply H_len_tl_st1.       
                                 ******* rewrite H_st2'.
                                         simpl.
                                         rewrite H_call_stack_st2.
                                         simpl.
                                         rewrite H_call_stack_st1 in H_lt_i_st1.
                                         simpl in H_lt_i_st1.
                                         apply H_lt_i_st1.
                                 ******* rewrite H_st2'.
                                         simpl.
                                         apply H_call_stack_st2.
                                 ******* apply H_len_tl_st1.       
                                 ******* apply H_equiv_sf1_sf2.
                                 ******* apply H_equiv_sf1_sf2.
                                 ******* apply H_equiv_sf1_sf2.
                                 ******* apply H_equiv_sf1_sf2.
                                 ******* apply H_equiv_sf1_sf2.
                                 ******* apply H_equiv_sf1_sf2.
                                 ******* apply H_equiv_sf1_sf2.
                          ****** apply H_live_at_pc.
                          ****** apply H_not_In_v_s.
                    ***** rewrite <- H_exec_inst_st1.
                          rewrite H_st2'.
                          unfold equiv_vars_in_top_frame.
                          simpl.
                          rewrite H_call_stack_st1.
                          rewrite H_call_stack_st2.
                          unfold equiv_stack_frames_up_to_v in H_equiv_sf1_sf2.
                          repeat split.
                          ****** rewrite H_fname_sf1.
                                 rewrite H_fname_sf2.
                                 reflexivity.
                          ****** rewrite H_bid_sf1.
                                 rewrite H_bid_sf2.
                                 reflexivity.
                          ****** rewrite H_pc_sf1.
                                 rewrite H_pc_sf2.
                                 reflexivity.
                          ****** intros v0 s0 H_accessed H_in_v0_s0.
                                 pose proof (accessed_var_instr_neq_v p fname bid b pc s0 v0 sout v H_b_exists H_live_at_pc H_not_In_v_s H_accessed H_in_v0_s0) as H_neq_v0_v.
                                 apply (H_equiv_assign_sf1_sf2 v0 H_neq_v0_v).
           *** remember (SmallStepD.StateD.set_status st2 (Status.Error "Function not found in call")) as st2' eqn:H_st2'.
               exists st2'.
               exists bid.
               exists b.
               exists pc.
               exists sout.
               repeat split.
               **** apply H_b_exists.
               **** left.
                    repeat split.
                    ***** rewrite <- H_exec_inst_st1.
                          simpl.
                          apply H_lt_i_st1.
                    ***** rewrite <- H_exec_inst_st1.
                          rewrite H_st2'.
                          simpl.
                          apply H_len_call_stack.
                    ***** rewrite <- H_exec_inst_st1.
                          rewrite H_st2'.
                          simpl.
                          reflexivity.
                    ***** rewrite <- H_exec_inst_st1.
                          rewrite H_st2'.
                          simpl.
                          apply H_dialect.
                    ***** exists [].
                          exists tl.
                          exists sf1.
                          exists sf2.
                          repeat split.
                          ****** rewrite <- H_exec_inst_st1.
                                 simpl.
                                 apply H_lt_i_st1.
                          ****** rewrite <- H_exec_inst_st1.
                                 simpl.
                                 apply H_call_stack_st1.
                          ****** apply H_len_tl_st1.      
                          ****** rewrite H_st2'.
                                 simpl.
                                 rewrite H_call_stack_st2.
                                 simpl.
                                 rewrite H_call_stack_st1 in H_lt_i_st1.
                                 simpl in H_lt_i_st1.
                                 apply H_lt_i_st1.
                          ****** rewrite H_st2'.
                                 simpl.
                                 apply H_call_stack_st2.
                          ****** apply H_len_tl_st2.
                          ****** apply H_equiv_sf1_sf2.        
                          ****** apply H_equiv_sf1_sf2.        
                          ****** apply H_equiv_sf1_sf2.        
                          ****** apply H_equiv_sf1_sf2.        
                          ****** apply H_equiv_sf1_sf2.        
                          ****** apply H_equiv_sf1_sf2.        
                          ****** apply H_equiv_sf1_sf2.
                    ***** apply H_live_at_pc.
                    ***** apply H_not_In_v_s.
               **** rewrite <- H_exec_inst_st1.
                    rewrite H_st2'.
                    unfold equiv_vars_in_top_frame.
                    simpl.
                    rewrite H_call_stack_st1.
                    rewrite H_call_stack_st2.
                    repeat split.
                    ***** rewrite H_fname_sf1.
                          rewrite H_fname_sf2.
                          reflexivity.
                    ***** rewrite H_bid_sf1.
                          rewrite H_bid_sf2.
                          reflexivity.
                    ***** rewrite H_pc_sf1.
                          rewrite H_pc_sf2.
                          reflexivity.
                    ***** intros v0 s0 H_accessed H_in_v0_s0.
                          pose proof (accessed_var_instr_neq_v p fname bid b pc s0 v0 sout v H_b_exists H_live_at_pc H_not_In_v_s H_accessed H_in_v0_s0) as H_neq_v0_v.
                          apply (H_equiv_assign_sf1_sf2 v0 H_neq_v0_v).
        ** rewrite <- H_dialect.
 
           destruct (D.execute_op_code (SmallStepD.StateD.dialect_state st1) op_call (SmallStepD.eval_sexpr (SmallStepD.SmartContractD.BlockD.InstructionD.input instr) sf1)) as [[output_values new_dialect_state] status].
 
           destruct (SmallStepD.VariableAssignmentD.assign_all (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) output_values) as [var_assignments'_sf1|] eqn:H_var_assignments'_sf1.

           *** pose proof (assign_all_some (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) output_values (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) var_assignments'_sf1 H_var_assignments'_sf1) as H_var_assignments'_sf2.
               destruct H_var_assignments'_sf2 as [var_assignments'_sf2 H_var_assignments'_sf2].
               rewrite H_var_assignments'_sf2.
               
               remember {|
                   Liveness_snd.StateD.call_stack :=
                     {|
                       Liveness_snd.StackFrameD.function_name :=
                         SmallStepD.StackFrameD.function_name sf2;
                       Liveness_snd.StackFrameD.variable_assignments := var_assignments'_sf2;
                       Liveness_snd.StackFrameD.curr_block_id :=
                         SmallStepD.StackFrameD.curr_block_id sf2;
                       Liveness_snd.StackFrameD.pc := SmallStepD.StackFrameD.pc sf2 + 1
                     |} :: tl;
                   Liveness_snd.StateD.status := status;
                   Liveness_snd.StateD.dialect_state := new_dialect_state
                 |} as st2' eqn:H_st2'.
               
               exists st2'.
               exists bid.
               exists b.
               exists (S pc).
               exists s.
               repeat split.
               **** apply H_b_exists.
               **** (* now we split on wether v in the output variables *)
                    pose proof (varlist_in_dec (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) v) as H_v_output.

                    destruct H_v_output as [H_v_in_output | H_v_not_in_output].

                    ***** right.
                          rewrite H_fname_sf1 in H_exec_inst_st1.
                          rewrite H_bid_sf1 in H_exec_inst_st1.
                          rewrite H_pc_sf1 in H_exec_inst_st1.
                          rewrite H_fname_sf2 in H_st2'.
                          rewrite H_bid_sf2 in H_st2'.
                          rewrite H_pc_sf2 in H_st2'.
                          
                          rewrite <- (assign_all_preserves_eq_up_to_eq (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) (StackFrameD.variable_assignments sf1) (StackFrameD.variable_assignments sf2) v output_values var_assignments'_sf1 var_assignments'_sf2 H_v_in_output H_equiv_assign_sf1_sf2  H_var_assignments'_sf1  H_var_assignments'_sf2) in H_st2'.
                          rewrite H_st2'.
                          rewrite <- H_exec_inst_st1.
                          reflexivity.
                  
                    ***** left.
                          repeat split.
                          ****** rewrite <- H_exec_inst_st1.
                                 simpl.
                                 rewrite H_call_stack_st1 in H_lt_i_st1.
                                 simpl in H_lt_i_st1.
                                 apply H_lt_i_st1.
                          ****** rewrite <- H_exec_inst_st1.
                                 rewrite H_st2'.
                                 simpl.
                                 reflexivity.
                          ****** rewrite <- H_exec_inst_st1.
                                 rewrite H_st2'.
                                 simpl.
                                 reflexivity.
                          ****** rewrite <- H_exec_inst_st1.
                                 rewrite H_st2'.
                                 simpl. 
                                 reflexivity.
                          ****** exists [].
                                 exists tl.
                                 exists {|
                                     Liveness_snd.StackFrameD.function_name :=
                                       SmallStepD.StackFrameD.function_name sf1;
                                     Liveness_snd.StackFrameD.variable_assignments := var_assignments'_sf1;
                                     Liveness_snd.StackFrameD.curr_block_id :=
                                       SmallStepD.StackFrameD.curr_block_id sf1;
                                     Liveness_snd.StackFrameD.pc := SmallStepD.StackFrameD.pc sf1 + 1
                                   |}.
                                 exists {|
                                     Liveness_snd.StackFrameD.function_name :=
                                       SmallStepD.StackFrameD.function_name sf2;
                                     Liveness_snd.StackFrameD.variable_assignments := var_assignments'_sf2;
                                     Liveness_snd.StackFrameD.curr_block_id :=
                                       SmallStepD.StackFrameD.curr_block_id sf2;
                                     Liveness_snd.StackFrameD.pc := SmallStepD.StackFrameD.pc sf2 + 1
                                   |}.
                                 repeat split.
                                 ******* rewrite <- H_exec_inst_st1.
                                         simpl.
                                         rewrite H_call_stack_st1 in H_lt_i_st1.
                                         simpl in H_lt_i_st1.
                                         apply H_lt_i_st1.
                                 ******* rewrite <- H_exec_inst_st1.
                                         simpl.
                                         reflexivity.
                                 ******* apply  H_len_tl_st1.
                                 ******* rewrite H_st2'.  
                                         simpl.
                                         rewrite H_call_stack_st2 in H_lt_i_st2.
                                         simpl in H_lt_i_st2.
                                         apply H_lt_i_st2.
                                 ******* rewrite H_st2'.
                                         simpl.
                                         reflexivity.
                                 ******* apply  H_len_tl_st2.
                                 ******* simpl.
                                         apply H_fname_sf1.
                                 ******* simpl.
                                         apply H_bid_sf1.
                                 ******* simpl.
                                         rewrite H_pc_sf1.
                                         rewrite Nat.add_comm.
                                         simpl.
                                         reflexivity.
                                 ******* simpl.
                                         apply H_fname_sf2.
                                 ******* simpl.
                                         apply H_bid_sf2.
                                 ******* simpl.
                                         rewrite H_pc_sf2.
                                         rewrite Nat.add_comm.
                                         simpl.
                                         reflexivity.
                                 ******* simpl.
                                         apply (assign_all_preserves_eq_up_to (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) v output_values var_assignments'_sf1 var_assignments'_sf2 H_v_not_in_output H_equiv_assign_sf1_sf2 H_var_assignments'_sf1 H_var_assignments'_sf2).
                 ****** apply H_live_at_S_pc.
                 ****** rewrite <- E_instr in H_sout.
                        apply (not_In_v_fwd v s sout instr H_sout H_not_In_v_s H_v_not_in_output).
           **** rewrite H_st2'.
                rewrite <- H_exec_inst_st1.
                unfold equiv_vars_in_top_frame.
                simpl.
                repeat split.
                ***** rewrite H_fname_sf1. rewrite H_fname_sf2. reflexivity.
                ***** rewrite H_bid_sf1. rewrite H_bid_sf2. reflexivity.
                ***** rewrite H_pc_sf1. rewrite H_pc_sf2. reflexivity.
                ***** intros v0 s0 H_accessed_vars H_in_v0_s0.           

                    (* wether v in output or not *)
                    pose proof (varlist_in_dec (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) v) as H_v_output.
                    destruct H_v_output as [H_v_in_output | H_v_not_in_output].

                    ****** rewrite (assign_all_preserves_eq_up_to_eq (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) (StackFrameD.variable_assignments sf1) (StackFrameD.variable_assignments sf2) v output_values var_assignments'_sf1 var_assignments'_sf2 H_v_in_output H_equiv_assign_sf1_sf2  H_var_assignments'_sf1  H_var_assignments'_sf2).
                           reflexivity.
                    ****** rewrite <- E_instr in H_sout.
                           pose proof (not_In_v_fwd v s sout instr H_sout H_not_In_v_s H_v_not_in_output) as H_not_In_v_s'.
                           pose proof (accessed_var_instr_neq_v p fname bid b (S pc) s0 v0 s v H_b_exists H_live_at_S_pc H_not_In_v_s' H_accessed_vars H_in_v0_s0) as H_v0_neq_v.
                               
                           apply (assign_all_preserves_eq_up_to (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) v output_values var_assignments'_sf1 var_assignments'_sf2 H_v_not_in_output H_equiv_assign_sf1_sf2 H_var_assignments'_sf1 H_var_assignments'_sf2 v0  H_v0_neq_v).

           *** rewrite (assign_all_none (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) output_values (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) H_var_assignments'_sf1).

             remember (SmallStepD.StateD.set_status st2 (Status.Error "Mismatch length in output variables and values in opcode execution")) as st2' eqn:H_st2'.
               exists st2'.
               exists bid.
               exists b.
               exists pc.
               exists sout.
               repeat split.
               **** apply H_b_exists.
               **** left.
                    repeat split.
                    ***** rewrite <- H_exec_inst_st1.
                          simpl.
                          apply H_lt_i.
                    ***** rewrite <- H_exec_inst_st1.
                          rewrite H_st2'.
                          simpl.
                          rewrite H_call_stack_st1.
                          rewrite H_call_stack_st2.
                          simpl.
                          reflexivity.
                    ***** rewrite <- H_exec_inst_st1.
                          rewrite H_st2'.
                          simpl.
                          reflexivity.
                    ***** rewrite <- H_exec_inst_st1.
                          rewrite H_st2'.
                          simpl.
                          apply H_dialect.
                    ***** exists [].
                          exists tl.
                          exists sf1.
                          exists sf2.
                          repeat split.
                          ****** rewrite <- H_exec_inst_st1.
                                 simpl.
                                 apply H_lt_i.
                          ****** rewrite <- H_exec_inst_st1.
                                 simpl.                     
                                 rewrite H_call_stack_st1.
                                 reflexivity.
                          ****** apply H_len_tl_st1.
                          ****** rewrite H_st2'.
                                 simpl.
                                 rewrite H_call_stack_st2.
                                 simpl.
                                 rewrite H_call_stack_st1 in H_lt_i.
                                 simpl in H_lt_i.
                                 apply H_lt_i.
                          ****** rewrite H_st2'.
                                 simpl.
                                 rewrite H_call_stack_st2.
                                 simpl.
                                 reflexivity.
                          ****** apply H_len_tl_st2.
                          ****** apply H_fname_sf1.
                          ****** apply H_bid_sf1.
                          ****** apply H_pc_sf1.
                          ****** apply H_fname_sf2.
                          ****** apply H_bid_sf2.
                          ****** apply H_pc_sf2.
                          ****** apply H_equiv_assign_sf1_sf2.
                    ***** apply H_live_at_pc.
                    ***** apply H_not_In_v_s.
               **** rewrite <- H_exec_inst_st1.
                    rewrite H_st2'.
                    unfold equiv_vars_in_top_frame.
                    simpl.
                    rewrite H_call_stack_st1.
                    rewrite H_call_stack_st2.
                    repeat split.
                    ***** rewrite H_fname_sf1. rewrite H_fname_sf2. reflexivity.
                    ***** rewrite H_bid_sf1. rewrite H_bid_sf2. reflexivity.
                    ***** rewrite H_pc_sf1. rewrite H_pc_sf2. reflexivity.
                    ***** intros v0 s0 H_accessed_var H_In_v0_s0.
                          pose proof (accessed_var_instr_neq_v p fname bid b pc s0 v0 sout v H_b_exists H_live_at_pc H_not_In_v_s H_accessed_var H_In_v0_s0) as H_v0_neq_v.
                          apply (H_equiv_assign_sf1_sf2 v0 H_v0_neq_v).
        ** rewrite <- H_dialect.
           remember (SmallStepD.eval_sexpr (SmallStepD.SmartContractD.BlockD.InstructionD.input instr) sf1) as output_values eqn:H_output_values.
  
           destruct (SmallStepD.VariableAssignmentD.assign_all (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) output_values) as [var_assignments'_sf1|] eqn:H_var_assignments'_sf1.

           *** pose proof (assign_all_some (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) output_values (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) var_assignments'_sf1 H_var_assignments'_sf1) as H_var_assignments'_sf2.
               destruct H_var_assignments'_sf2 as [var_assignments'_sf2 H_var_assignments'_sf2].
               rewrite H_var_assignments'_sf2.

               rewrite <- H_status.
               remember {|
                           Liveness_snd.StateD.call_stack :=
                            {|
                              Liveness_snd.StackFrameD.function_name := SmallStepD.StackFrameD.function_name sf2;
                              Liveness_snd.StackFrameD.variable_assignments := var_assignments'_sf2;
                              Liveness_snd.StackFrameD.curr_block_id := SmallStepD.StackFrameD.curr_block_id sf2;
                              Liveness_snd.StackFrameD.pc := SmallStepD.StackFrameD.pc sf2 + 1
                            |} :: tl;
                          Liveness_snd.StateD.status := SmallStepD.StateD.status st1;
                          Liveness_snd.StateD.dialect_state := StateD.dialect_state st1
                 |} as st2' eqn:H_st2'.
               
               exists st2'.
               exists bid.
               exists b.
               exists (S pc).
               exists s.
               repeat split.
               **** apply H_b_exists.
               **** (* now we split on wether v in the output variables *)
                    pose proof (varlist_in_dec (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) v) as H_v_output.

                    destruct H_v_output as [H_v_in_output | H_v_not_in_output].

                    ***** right.
                          rewrite H_fname_sf1 in H_exec_inst_st1.
                          rewrite H_bid_sf1 in H_exec_inst_st1.
                          rewrite H_pc_sf1 in H_exec_inst_st1.
                          rewrite H_fname_sf2 in H_st2'.
                          rewrite H_bid_sf2 in H_st2'.
                          rewrite H_pc_sf2 in H_st2'.
                          
                          rewrite <- (assign_all_preserves_eq_up_to_eq (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) (StackFrameD.variable_assignments sf1) (StackFrameD.variable_assignments sf2) v output_values var_assignments'_sf1 var_assignments'_sf2 H_v_in_output H_equiv_assign_sf1_sf2  H_var_assignments'_sf1  H_var_assignments'_sf2) in H_st2'.
                          rewrite H_st2'.
                          rewrite <- H_exec_inst_st1.
                          reflexivity.
                  
                    ***** left.
                          repeat split.
                          ****** rewrite <- H_exec_inst_st1.
                                 simpl.
                                 rewrite H_call_stack_st1 in H_lt_i_st1.
                                 simpl in H_lt_i_st1.
                                 apply H_lt_i_st1.
                          ****** rewrite <- H_exec_inst_st1.
                                 rewrite H_st2'.
                                 simpl.
                                 reflexivity.
                          ****** rewrite <- H_exec_inst_st1.
                                 rewrite H_st2'.
                                 simpl.
                                 reflexivity.
                          ****** rewrite <- H_exec_inst_st1.
                                 rewrite H_st2'.
                                 simpl. 
                                 reflexivity.
                          ****** exists [].
                                 exists tl.
                                 exists {|
                                     Liveness_snd.StackFrameD.function_name :=
                                       SmallStepD.StackFrameD.function_name sf1;
                                     Liveness_snd.StackFrameD.variable_assignments := var_assignments'_sf1;
                                     Liveness_snd.StackFrameD.curr_block_id :=
                                       SmallStepD.StackFrameD.curr_block_id sf1;
                                     Liveness_snd.StackFrameD.pc := SmallStepD.StackFrameD.pc sf1 + 1
                                   |}.
                                 exists {|
                                     Liveness_snd.StackFrameD.function_name :=
                                       SmallStepD.StackFrameD.function_name sf2;
                                     Liveness_snd.StackFrameD.variable_assignments := var_assignments'_sf2;
                                     Liveness_snd.StackFrameD.curr_block_id :=
                                       SmallStepD.StackFrameD.curr_block_id sf2;
                                     Liveness_snd.StackFrameD.pc := SmallStepD.StackFrameD.pc sf2 + 1
                                   |}.
                                 repeat split.
                                 ******* rewrite <- H_exec_inst_st1.
                                         simpl.
                                         rewrite H_call_stack_st1 in H_lt_i_st1.
                                         simpl in H_lt_i_st1.
                                         apply H_lt_i_st1.
                                 ******* rewrite <- H_exec_inst_st1.
                                         simpl.
                                         reflexivity.
                                 ******* apply  H_len_tl_st1.
                                 ******* rewrite H_st2'.  
                                         simpl.
                                         rewrite H_call_stack_st2 in H_lt_i_st2.
                                         simpl in H_lt_i_st2.
                                         apply H_lt_i_st2.
                                 ******* rewrite H_st2'.
                                         simpl.
                                         reflexivity.
                                 ******* apply  H_len_tl_st2.
                                 ******* simpl.
                                         apply H_fname_sf1.
                                 ******* simpl.
                                         apply H_bid_sf1.
                                 ******* simpl.
                                         rewrite H_pc_sf1.
                                         rewrite Nat.add_comm.
                                         simpl.
                                         reflexivity.
                                 ******* simpl.
                                         apply H_fname_sf2.
                                 ******* simpl.
                                         apply H_bid_sf2.
                                 ******* simpl.
                                         rewrite H_pc_sf2.
                                         rewrite Nat.add_comm.
                                         simpl.
                                         reflexivity.
                                 ******* simpl.
                                         apply (assign_all_preserves_eq_up_to (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) v output_values var_assignments'_sf1 var_assignments'_sf2 H_v_not_in_output H_equiv_assign_sf1_sf2 H_var_assignments'_sf1 H_var_assignments'_sf2).
                 ****** apply H_live_at_S_pc.
                 ****** rewrite <- E_instr in H_sout.
                        apply (not_In_v_fwd v s sout instr H_sout H_not_In_v_s H_v_not_in_output).
           **** rewrite H_st2'.
                rewrite <- H_exec_inst_st1.
                unfold equiv_vars_in_top_frame.
                simpl.
                repeat split.
                ***** rewrite H_fname_sf1. rewrite H_fname_sf2. reflexivity.
                ***** rewrite H_bid_sf1. rewrite H_bid_sf2. reflexivity.
                ***** rewrite H_pc_sf1. rewrite H_pc_sf2. reflexivity.
                ***** intros v0 s0 H_accessed_vars H_in_v0_s0.           

                    (* wether v in output or not *)
                    pose proof (varlist_in_dec (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) v) as H_v_output.
                    destruct H_v_output as [H_v_in_output | H_v_not_in_output].

                    ****** rewrite (assign_all_preserves_eq_up_to_eq (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) (StackFrameD.variable_assignments sf1) (StackFrameD.variable_assignments sf2) v output_values var_assignments'_sf1 var_assignments'_sf2 H_v_in_output H_equiv_assign_sf1_sf2  H_var_assignments'_sf1  H_var_assignments'_sf2).
                           reflexivity.
                    ****** rewrite <- E_instr in H_sout.
                           pose proof (not_In_v_fwd v s sout instr H_sout H_not_In_v_s H_v_not_in_output) as H_not_In_v_s'.
                           pose proof (accessed_var_instr_neq_v p fname bid b (S pc) s0 v0 s v H_b_exists H_live_at_S_pc H_not_In_v_s' H_accessed_vars H_in_v0_s0) as H_v0_neq_v.
                               
                           apply (assign_all_preserves_eq_up_to (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) v output_values var_assignments'_sf1 var_assignments'_sf2 H_v_not_in_output H_equiv_assign_sf1_sf2 H_var_assignments'_sf1 H_var_assignments'_sf2 v0  H_v0_neq_v).

           *** rewrite (assign_all_none (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) output_values (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) H_var_assignments'_sf1).
  
             remember (SmallStepD.StateD.set_status st2 (Status.Error "Mismatch length in output variables and values in assignment instruction")) as st2' eqn:H_st2'.
               exists st2'.
               exists bid.
               exists b.
               exists pc.
               exists sout.
               repeat split.
               **** apply H_b_exists.
               **** left.
                    repeat split.
                    ***** rewrite <- H_exec_inst_st1.
                          simpl.
                          apply H_lt_i.
                    ***** rewrite <- H_exec_inst_st1.
                          rewrite H_st2'.
                          simpl.
                          rewrite H_call_stack_st1.
                          rewrite H_call_stack_st2.
                          simpl.
                          reflexivity.
                    ***** rewrite <- H_exec_inst_st1.
                          rewrite H_st2'.
                          simpl.
                          reflexivity.
                    ***** rewrite <- H_exec_inst_st1.
                          rewrite H_st2'.
                          simpl.
                          apply H_dialect.
                    ***** exists [].
                          exists tl.
                          exists sf1.
                          exists sf2.
                          repeat split.
                          ****** rewrite <- H_exec_inst_st1.
                                 simpl.
                                 apply H_lt_i.
                          ****** rewrite <- H_exec_inst_st1.
                                 simpl.                     
                                 rewrite H_call_stack_st1.
                                 reflexivity.
                          ****** apply H_len_tl_st1.
                          ****** rewrite H_st2'.
                                 simpl.
                                 rewrite H_call_stack_st2.
                                 simpl.
                                 rewrite H_call_stack_st1 in H_lt_i.
                                 simpl in H_lt_i.
                                 apply H_lt_i.
                          ****** rewrite H_st2'.
                                 simpl.
                                 rewrite H_call_stack_st2.
                                 simpl.
                                 reflexivity.
                          ****** apply H_len_tl_st2.
                          ****** apply H_fname_sf1.
                          ****** apply H_bid_sf1.
                          ****** apply H_pc_sf1.
                          ****** apply H_fname_sf2.
                          ****** apply H_bid_sf2.
                          ****** apply H_pc_sf2.
                          ****** apply H_equiv_assign_sf1_sf2.
                    ***** apply H_live_at_pc.
                    ***** apply H_not_In_v_s.
               **** rewrite <- H_exec_inst_st1.
                    rewrite H_st2'.
                    unfold equiv_vars_in_top_frame.
                    simpl.
                    rewrite H_call_stack_st1.
                    rewrite H_call_stack_st2.
                    repeat split.
                    ***** rewrite H_fname_sf1. rewrite H_fname_sf2. reflexivity.
                    ***** rewrite H_bid_sf1. rewrite H_bid_sf2. reflexivity.
                    ***** rewrite H_pc_sf1. rewrite H_pc_sf2. reflexivity.
                    ***** intros v0 s0 H_accessed_var H_In_v0_s0.
                          pose proof (accessed_var_instr_neq_v p fname bid b pc s0 v0 sout v H_b_exists H_live_at_pc H_not_In_v_s H_accessed_var H_In_v0_s0) as H_v0_neq_v.
                          apply (H_equiv_assign_sf1_sf2 v0 H_v0_neq_v).

    (* the case where the top stack frames are identical, and the one with v is deeper *)
    + simpl in H_call_stack_st1.
      simpl in H_call_stack_st2.
      
      unfold SmallStepD.execute_instr in H_exec_inst_st1.
      rewrite H_call_stack_st1 in H_exec_inst_st1.

      unfold SmallStepD.execute_instr.
      rewrite H_call_stack_st2.

      destruct (SmallStepD.SmartContractD.BlockD.InstructionD.op instr) as [ f_or_op | assignment ] eqn:E_op; try destruct f_or_op as [f_call | op_call].

      * destruct (SmallStepD.SmartContractD.get_function p f_call) eqn:E_fcall; try discriminate.

        ** destruct (SmallStepD.CallStackD.StackFrameD.VariableAssignmentD.assign_all SmallStepD.CallStackD.StackFrameD.VariableAssignmentD.empty (SmallStepD.SmartContractD.FunctionD.arguments t) (SmallStepD.eval_sexpr (SmallStepD.SmartContractD.BlockD.InstructionD.input instr) top_sf)) eqn:E_assignment.

           *** remember
               {|
                 Liveness_snd.StateD.call_stack :=
                   {|
                     Liveness_snd.StackFrameD.function_name := f_call;
                     Liveness_snd.StackFrameD.variable_assignments := t0;
                     Liveness_snd.StackFrameD.curr_block_id :=
                       SmallStepD.SmartContractD.FunctionD.entry_block_id t;
                     Liveness_snd.StackFrameD.pc := 0;
                   |} :: top_sf :: hl' ++ sf2 :: tl;
                 Liveness_snd.StateD.status := SmallStepD.StateD.status st2;
                 Liveness_snd.StateD.dialect_state := SmallStepD.StateD.dialect_state st2
               |}
               as st2' eqn:H_st2'.
               
               exists st2'.
               exists bid.
               exists b.
               exists pc.
               exists s.
               repeat split.
               **** apply H_b_exists.
               **** left.
                    repeat split.
                    ***** rewrite <- H_exec_inst_st1.
                          simpl.
                          rewrite H_call_stack_st1 in H_lt_i.
                          simpl in H_lt_i.
                          apply (Nat.lt_trans i (S (length (hl' ++ sf1 :: tl))) (S (S (length (hl' ++ sf1 :: tl)))) H_lt_i (Nat.lt_succ_diag_r (S (length (hl' ++ sf1 :: tl))))).
                    ***** rewrite <- H_exec_inst_st1.
                          rewrite H_st2'.
                          simpl.
                          repeat rewrite length_app.
                          simpl.
                          reflexivity.
                    ***** rewrite <- H_exec_inst_st1.
                          rewrite H_st2'.
                          simpl.
                          apply H_status.
                    ***** rewrite <- H_exec_inst_st1.
                          rewrite H_st2'.
                          simpl.
                          apply H_dialect.
                    ***** remember {|
                              Liveness_snd.StackFrameD.function_name := f_call;
                              Liveness_snd.StackFrameD.variable_assignments := t0;
                              Liveness_snd.StackFrameD.curr_block_id :=
                                SmallStepD.SmartContractD.FunctionD.entry_block_id t;
                              Liveness_snd.StackFrameD.pc := 0;
                            |} as new_sf_top eqn:H_new_sf_top.
                         exists (new_sf_top :: top_sf :: hl').
                         exists tl.
                         exists sf1.
                         exists sf2.
                         repeat split.
                         ****** rewrite <- H_exec_inst_st1.
                                simpl.
                                rewrite H_call_stack_st1 in H_lt_i.
                                simpl in H_lt_i.
                                apply (Nat.lt_trans i (S (length (hl' ++ sf1 :: tl))) (S (S (length (hl' ++ sf1 :: tl)))) H_lt_i (Nat.lt_succ_diag_r (S (length (hl' ++ sf1 :: tl))))).
                         ****** rewrite <- H_exec_inst_st1.
                                simpl.
                                reflexivity.
                         ****** apply H_len_tl_st1.
                         ****** rewrite H_st2'.
                                simpl.
                                rewrite H_call_stack_st2 in H_lt_i_st2.
                                simpl in H_lt_i_st2.
                                apply (Nat.lt_trans i (S (length (hl' ++ sf2 :: tl))) (S (S (length (hl' ++ sf2 :: tl)))) H_lt_i_st2 (Nat.lt_succ_diag_r (S (length (hl' ++ sf2 :: tl))))).
                         ****** rewrite H_st2'.
                                simpl.
                                reflexivity.
                         ****** apply H_len_tl_st2.
                         ****** apply H_equiv_sf1_sf2.
                         ****** apply H_equiv_sf1_sf2.
                         ****** apply H_equiv_sf1_sf2.
                         ****** apply H_equiv_sf1_sf2.
                         ****** apply H_equiv_sf1_sf2.
                         ****** apply H_equiv_sf1_sf2.
                         ****** apply H_equiv_sf1_sf2.
                    ***** apply H_live_at_pc.
                    ***** apply H_not_In_v_s.
               **** unfold equiv_vars_in_top_frame.
                    rewrite <- H_exec_inst_st1.
                    rewrite H_st2'.
                    simpl.
                    repeat split; try reflexivity.
           *** remember (SmallStepD.StateD.set_status st2 (Status.Error "Failed to create initial variable assignment")) as st2' eqn:H_st2'.
               exists st2'.
               exists bid.
               exists b.
               exists pc.
               exists s.
               repeat split.
               **** apply H_b_exists.
               **** left.
                    repeat split.
                    ***** rewrite <- H_exec_inst_st1.
                          simpl.
                          apply H_lt_i.
                    ***** rewrite <- H_exec_inst_st1.
                          rewrite H_st2'.
                          simpl.
                          apply H_len_call_stack.
                    ***** rewrite <- H_exec_inst_st1.
                          rewrite H_st2'.
                          simpl.
                          reflexivity.
                    ***** rewrite <- H_exec_inst_st1.
                          rewrite H_st2'.
                          simpl.
                          apply H_dialect.
                    ***** exists (top_sf :: hl').
                          exists tl.
                          exists sf1.
                          exists sf2.
                          repeat split.
                          ****** rewrite <- H_exec_inst_st1.
                                 simpl.
                                 apply H_lt_i.
                          ****** rewrite <- H_exec_inst_st1.
                                 simpl.
                                 apply H_call_stack_st1.
                          ****** apply H_len_tl_st1.
                          ****** rewrite H_st2'.
                                 simpl.
                                 rewrite H_call_stack_st2.
                                 simpl.
                                 rewrite length_app.
                                 simpl.
                                 rewrite H_call_stack_st1 in H_lt_i.
                                 simpl in  H_lt_i.
                                 rewrite length_app in H_lt_i.
                                 simpl in H_lt_i.
                                 apply H_lt_i.
                          ****** rewrite H_st2'.       
                                 simpl.
                                 apply H_call_stack_st2.
                          ****** apply H_len_tl_st2.
                          ****** apply H_equiv_sf1_sf2.
                          ****** apply H_equiv_sf1_sf2.
                          ****** apply H_equiv_sf1_sf2.
                          ****** apply H_equiv_sf1_sf2.
                          ****** apply H_equiv_sf1_sf2.
                          ****** apply H_equiv_sf1_sf2.
                          ****** apply H_equiv_sf1_sf2.
                    ***** apply H_live_at_pc.                              
                    ***** apply H_not_In_v_s.
               **** rewrite H_st2'.
                    rewrite <- H_exec_inst_st1.
                    unfold equiv_vars_in_top_frame.
                    repeat rewrite <- (set_status_preserves_call_stack).
                    rewrite H_call_stack_st1.
                    rewrite H_call_stack_st2.
                    repeat split; try reflexivity.
        ** remember (SmallStepD.StateD.set_status st2 (Status.Error "Function not found in call")) as st2' eqn:H_st2'.
           exists st2'.
           exists bid.
           exists b.
           exists pc.
           exists s.
           repeat split.
           *** apply H_b_exists.
           *** left.
               repeat split.
               **** rewrite <- H_exec_inst_st1.
                    rewrite <- (set_status_preserves_call_stack).
                    apply H_lt_i.
               **** rewrite <- H_exec_inst_st1.
                    rewrite H_st2'.
                    simpl.
                    apply H_len_call_stack.
               **** rewrite <- H_exec_inst_st1.
                    rewrite H_st2'.
                    simpl.
                    reflexivity.
               **** rewrite <- H_exec_inst_st1.
                    rewrite H_st2'.
                    simpl.
                    apply H_dialect.
               **** exists (top_sf :: hl').
                    exists tl.
                    exists sf1.
                    exists sf2.
                    repeat split.
                    ***** rewrite <- H_exec_inst_st1.
                          simpl.
                          apply H_lt_i.
                    ***** rewrite <- H_exec_inst_st1.
                          simpl.
                          apply H_call_stack_st1.
                    ***** apply H_len_tl_st1.
                    ***** rewrite H_st2'.
                          simpl.
                          rewrite H_call_stack_st2.
                          simpl.
                          rewrite length_app.
                          simpl.
                          rewrite H_call_stack_st1 in H_lt_i.
                          simpl in  H_lt_i.
                          rewrite length_app in H_lt_i.
                          simpl in H_lt_i.
                          apply H_lt_i.
                    ***** rewrite H_st2'.       
                          simpl.
                          apply H_call_stack_st2.
                    ***** apply H_len_tl_st2.
                    ***** apply H_equiv_sf1_sf2.
                    ***** apply H_equiv_sf1_sf2.
                    ***** apply H_equiv_sf1_sf2.
                    ***** apply H_equiv_sf1_sf2.
                    ***** apply H_equiv_sf1_sf2.
                    ***** apply H_equiv_sf1_sf2.
                    ***** apply H_equiv_sf1_sf2.
               **** apply H_live_at_pc.                              
               **** apply H_not_In_v_s.
           *** rewrite H_st2'.
               rewrite <- H_exec_inst_st1.
               unfold equiv_vars_in_top_frame.
               repeat rewrite <- (set_status_preserves_call_stack).
               rewrite H_call_stack_st1.
               rewrite H_call_stack_st2.
               repeat split; try reflexivity.
      * rewrite <- (equiv_states_eq_dialect p i fname bid pc v st1 st2 H_equiv_st1_st2).

        destruct (D.execute_op_code (StateD.dialect_state st1) op_call (SmallStepD.eval_sexpr (SmallStepD.SmartContractD.BlockD.InstructionD.input instr) top_sf)) as [ [output_values new_dialect_state] status] eqn:E_D_exec.

        destruct (SmallStepD.VariableAssignmentD.assign_all (SmallStepD.StackFrameD.variable_assignments top_sf) (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) output_values) eqn:E_assign_all.

        ** remember {|
               Liveness_snd.StateD.call_stack :=
                 {|
                   Liveness_snd.StackFrameD.function_name := SmallStepD.StackFrameD.function_name top_sf;
                   Liveness_snd.StackFrameD.variable_assignments := t;
                   Liveness_snd.StackFrameD.curr_block_id := SmallStepD.StackFrameD.curr_block_id top_sf;
                   Liveness_snd.StackFrameD.pc := SmallStepD.StackFrameD.pc top_sf + 1;
                 |} :: hl' ++ sf2 :: tl;
               Liveness_snd.StateD.status := status;
               Liveness_snd.StateD.dialect_state := new_dialect_state
             |}
             as st2' eqn:H_st2'.

           exists st2'.
           exists bid.
           exists b.
           exists pc.
           exists s.
           repeat split.
           *** apply H_b_exists.
           *** left.
               repeat split.
               **** rewrite <- H_exec_inst_st1.
                    rewrite H_call_stack_st1  in H_lt_i.
                    simpl in H_lt_i.
                    apply H_lt_i.
               **** rewrite <- H_exec_inst_st1.
                    rewrite H_st2'.
                    simpl.
                    repeat rewrite length_app.
                    simpl.
                    reflexivity.
               **** rewrite <- H_exec_inst_st1.
                    rewrite H_st2'.
                    simpl.
                    reflexivity.
               **** rewrite <- H_exec_inst_st1.
                    rewrite H_st2'.
                    simpl.
                    reflexivity.
               **** exists ({|
                        Liveness_snd.StackFrameD.function_name := SmallStepD.StackFrameD.function_name top_sf;
                        Liveness_snd.StackFrameD.variable_assignments := t;
                        Liveness_snd.StackFrameD.curr_block_id := SmallStepD.StackFrameD.curr_block_id top_sf;
                        Liveness_snd.StackFrameD.pc := SmallStepD.StackFrameD.pc top_sf + 1;
                             |} :: hl').
                    exists tl.
                    exists sf1.
                    exists sf2.
                    repeat split.
                    ***** rewrite <- H_exec_inst_st1.
                          rewrite H_call_stack_st1  in H_lt_i.
                          simpl in H_lt_i.
                          apply H_lt_i.
                    ***** rewrite <- H_exec_inst_st1.
                          simpl.
                          reflexivity.
                    ***** apply H_len_tl_st1.
                    ***** rewrite H_st2'.
                          simpl.
                          rewrite length_app.
                          simpl.
                          rewrite H_call_stack_st1  in H_lt_i.
                          simpl in H_lt_i.
                          rewrite length_app in  H_lt_i.
                          simpl in H_lt_i.
                          apply H_lt_i.
                    ***** rewrite H_st2'.
                          simpl.
                          reflexivity.
                    ***** apply H_len_tl_st1.
                    ***** apply H_equiv_sf1_sf2.
                    ***** apply H_equiv_sf1_sf2.
                    ***** apply H_equiv_sf1_sf2.
                    ***** apply H_equiv_sf1_sf2.
                    ***** apply H_equiv_sf1_sf2.
                    ***** apply H_equiv_sf1_sf2.
                    ***** apply H_equiv_sf1_sf2.
               **** apply H_live_at_pc.
               **** apply H_not_In_v_s.
           *** rewrite <- H_exec_inst_st1.
               rewrite H_st2'.
               unfold equiv_vars_in_top_frame.
               simpl.
               repeat split; try reflexivity.
        ** remember (SmallStepD.StateD.set_status st2 (Status.Error "Mismatch length in output variables and values in opcode execution")) as st2' eqn:H_st2'.
           exists st2'.
           exists bid.
           exists b.
           exists pc.
           exists s.
           repeat split.
           *** apply H_b_exists.
           *** left.
               repeat split.
               **** rewrite <- H_exec_inst_st1.
                    simpl.
                    apply H_lt_i.
               **** rewrite <- H_exec_inst_st1.
                    rewrite H_st2'.
                    simpl.
                    apply H_len_call_stack.
               **** rewrite <- H_exec_inst_st1.
                    rewrite H_st2'.
                    simpl.
                    reflexivity.
               **** rewrite <- H_exec_inst_st1.
                    rewrite H_st2'.
                    simpl.
                    apply H_dialect.
               **** exists (top_sf :: hl').
                    exists tl.
                    exists sf1.
                    exists sf2.
                    repeat split.
                    ***** rewrite  <- H_exec_inst_st1.
                          simpl.
                          apply H_lt_i.
                    ***** rewrite <- H_exec_inst_st1.
                          simpl.
                          apply H_call_stack_st1.
                    ***** apply H_len_tl_st1.
                    ***** rewrite H_st2'.
                          simpl.
                          rewrite H_call_stack_st2.
                          simpl.
                          rewrite length_app.
                          simpl.
                          rewrite H_call_stack_st1  in H_lt_i.
                          simpl in H_lt_i.
                          rewrite length_app in  H_lt_i.
                          simpl in H_lt_i.
                          apply H_lt_i.
                    ***** rewrite H_st2'.
                          simpl.
                          apply H_call_stack_st2.
                    ***** apply H_len_tl_st1.
                    ***** apply H_equiv_sf1_sf2.  
                    ***** apply H_equiv_sf1_sf2.  
                    ***** apply H_equiv_sf1_sf2.  
                    ***** apply H_equiv_sf1_sf2.  
                    ***** apply H_equiv_sf1_sf2.  
                    ***** apply H_equiv_sf1_sf2. 
                    ***** apply H_equiv_sf1_sf2.  
               **** apply H_live_at_pc.
               **** apply H_not_In_v_s.
           *** rewrite <- H_exec_inst_st1.
               rewrite H_st2'.
               unfold equiv_vars_in_top_frame.
               simpl.
               rewrite H_call_stack_st1.
               rewrite H_call_stack_st2.
               repeat split; try reflexivity.
      * destruct (SmallStepD.VariableAssignmentD.assign_all (SmallStepD.StackFrameD.variable_assignments top_sf) (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) (SmallStepD.eval_sexpr (SmallStepD.SmartContractD.BlockD.InstructionD.input instr) top_sf)).
        ** rewrite <- (equiv_states_eq_dialect p i fname bid pc v st1 st2 H_equiv_st1_st2).
           remember {|
               Liveness_snd.StateD.call_stack :=
                 {|
                   Liveness_snd.StackFrameD.function_name := SmallStepD.StackFrameD.function_name top_sf;
                   Liveness_snd.StackFrameD.variable_assignments := t;
                   Liveness_snd.StackFrameD.curr_block_id := SmallStepD.StackFrameD.curr_block_id top_sf;
                   Liveness_snd.StackFrameD.pc := SmallStepD.StackFrameD.pc top_sf + 1;
        |} :: hl' ++ sf2 :: tl;
               Liveness_snd.StateD.status := SmallStepD.StateD.status st2;
               Liveness_snd.StateD.dialect_state := StateD.dialect_state st1
             |} as st2' eqn:H_st2'.

           exists st2'.
           exists bid.
           exists b.
           exists pc.
           exists s.
           repeat split.
           *** apply H_b_exists.
           *** left.
               repeat split.
               **** rewrite <- H_exec_inst_st1.
                    rewrite H_call_stack_st1  in H_lt_i.
                    simpl in H_lt_i.
                    apply H_lt_i.
               **** rewrite <- H_exec_inst_st1.
                    rewrite H_st2'.
                    simpl.
                    repeat rewrite length_app.
                    simpl.
                    reflexivity.
               **** rewrite <- H_exec_inst_st1.
                    rewrite H_st2'.
                    simpl.
                    apply H_status.
               **** rewrite <- H_exec_inst_st1.
                    rewrite H_st2'.
                    simpl.
                    reflexivity.
               **** exists ({|
                               Liveness_snd.StackFrameD.function_name := SmallStepD.StackFrameD.function_name top_sf;
                               Liveness_snd.StackFrameD.variable_assignments := t;
                               Liveness_snd.StackFrameD.curr_block_id := SmallStepD.StackFrameD.curr_block_id top_sf;
                               Liveness_snd.StackFrameD.pc := SmallStepD.StackFrameD.pc top_sf + 1;
                                |} :: hl').
                    exists tl.
                    exists sf1.
                    exists sf2.
                    repeat split.
                    ***** rewrite <- H_exec_inst_st1.
                          simpl.
                          rewrite length_app.
                          simpl.
                          rewrite H_call_stack_st1 in H_lt_i_st1.
                          simpl in H_lt_i_st1.
                          rewrite length_app in H_lt_i_st1.
                          simpl in H_lt_i_st1.
                          apply H_lt_i_st1.
                   ***** rewrite <- H_exec_inst_st1.
                         simpl.
                         reflexivity.
                   ***** apply H_len_tl_st1.
                   ***** rewrite H_st2'.    
                         simpl.
                         rewrite length_app.
                         simpl.
                         rewrite H_call_stack_st1 in H_lt_i_st1.
                         simpl in H_lt_i_st1.
                         rewrite length_app in H_lt_i_st1.
                         simpl in H_lt_i_st1.
                         apply H_lt_i_st1.
                   ***** rewrite H_st2'.
                         simpl.
                         reflexivity.
                   ***** apply H_len_tl_st2.
                   ***** apply H_equiv_sf1_sf2.
                   ***** apply H_equiv_sf1_sf2.
                   ***** apply H_equiv_sf1_sf2.
                   ***** apply H_equiv_sf1_sf2.
                   ***** apply H_equiv_sf1_sf2.
                   ***** apply H_equiv_sf1_sf2.
                   ***** apply H_equiv_sf1_sf2.
               **** apply H_live_at_pc.
               **** apply H_not_In_v_s.
           *** rewrite <- H_exec_inst_st1.
               rewrite H_st2'.
               unfold equiv_vars_in_top_frame.
               simpl.
               repeat split; reflexivity.
        ** remember (SmallStepD.StateD.set_status st2 (Status.Error "Mismatch length in output variables and values in assignment instruction")) as st2' eqn:H_st2'.
           exists st2'.
           exists bid.
           exists b.
           exists pc.
           exists s.
           repeat split.
           *** apply H_b_exists.
           *** left.
               repeat split.
               **** rewrite <- H_exec_inst_st1.
                    simpl.
                    apply H_lt_i.
               **** rewrite <- H_exec_inst_st1.
                    rewrite H_st2'.
                    simpl.
                    apply H_len_call_stack.
               **** rewrite <- H_exec_inst_st1.
                    rewrite H_st2'.
                    simpl.
                    reflexivity.
               **** rewrite <- H_exec_inst_st1.
                    rewrite H_st2'.
                    simpl.
                    apply H_dialect.
               **** exists (top_sf :: hl').
                    exists tl.
                    exists sf1.
                    exists sf2.
                    repeat split.
                    ***** rewrite  <- H_exec_inst_st1.
                          simpl.
                          apply H_lt_i.
                    ***** rewrite <- H_exec_inst_st1.
                          simpl.
                          apply H_call_stack_st1.
                    ***** apply H_len_tl_st1.
                    ***** rewrite H_st2'.
                          simpl.
                          rewrite H_call_stack_st2.
                          simpl.
                          rewrite length_app.
                          simpl.
                          rewrite H_call_stack_st1  in H_lt_i.
                          simpl in H_lt_i.
                          rewrite length_app in  H_lt_i.
                          simpl in H_lt_i.
                          apply H_lt_i.
                    ***** rewrite H_st2'.
                          simpl.
                          apply H_call_stack_st2.
                    ***** apply H_len_tl_st1.
                    ***** apply H_equiv_sf1_sf2.  
                    ***** apply H_equiv_sf1_sf2.  
                    ***** apply H_equiv_sf1_sf2.  
                    ***** apply H_equiv_sf1_sf2.  
                    ***** apply H_equiv_sf1_sf2.  
                    ***** apply H_equiv_sf1_sf2. 
                    ***** apply H_equiv_sf1_sf2.  
               **** apply H_live_at_pc.
               **** apply H_not_In_v_s.
           *** rewrite <- H_exec_inst_st1.
               rewrite H_st2'.
               unfold equiv_vars_in_top_frame.
               simpl.
               rewrite H_call_stack_st1.
               rewrite H_call_stack_st2.
               repeat split; try reflexivity.
  Qed.

  Fixpoint search_renamings_split (l: YULVariableMapD.t) (v: YULVariable.t) 
    : (YULVariableMapD.t * option YULVariableMapD.SimpleExprD.t * YULVariableMapD.t) :=
    match l with
    | [] => (l, None, l) (* No dummy value needed! *)
    | (v',sexpr)::l' =>
        if (YULVariable.eqb v' v)
        then ([], Some sexpr, l')
        else match search_renamings_split l' v with
             | (hl, res, tl) => ((v',sexpr)::hl, res, tl)
             end
    end.

  
  
  Lemma renaming_split_true:
    forall (l hl tl: YULVariableMapD.t) (v: YULVariable.t) (sexpr: SimpleExprD.t),
      search_renamings_split l v = (hl, Some sexpr, tl) ->
      l = hl++(v, sexpr)::tl.
  Proof.
    induction l as [|e l' IHl'].
    - intros hl tl v sexpr H_search.
      simpl in H_search.
      discriminate H_search.
    - intros hl tl v sexpr H_search.
      simpl in H_search.
      destruct e as [v' sexpr'] eqn:E_e.
      destruct (YULVariable.eqb v' v) eqn:E_eqb_v'_v.
      + injection H_search as H_hl H_sexpr H_tl.
        rewrite <- H_hl.
        rewrite <- H_sexpr.
        rewrite <- H_tl.
        simpl.
        unfold YULVariable.eqb in E_eqb_v'_v.
        rewrite Nat.eqb_eq in E_eqb_v'_v.
        rewrite E_eqb_v'_v.
        reflexivity.
      + destruct (search_renamings_split l' v) as [[hl' [sexpr''|]] tl'] eqn:E_search_rec; try discriminate.
        pose proof (IHl' hl' tl' v sexpr'' E_search_rec) as IHl'_0.
        injection H_search as H_hl H_sexpr H_tl.
        subst tl'.
        subst l'.
        subst sexpr''.
        subst hl.
        simpl.
        reflexivity.
  Qed.

  Lemma renaming_split_true_not_In:
    forall (l hl tl: YULVariableMapD.t) (v: YULVariable.t) (sexpr: SimpleExprD.t),
      search_renamings_split l v = (hl, Some sexpr, tl) ->
      forall sexpr, ~ List.In (v,sexpr) hl.
  Proof.
      induction l as [|e l' IHl'].
    - intros hl tl v sexpr H_search.
      simpl in H_search.
      discriminate H_search.
    - intros hl tl v sexpr H_search.
      simpl in H_search.
      destruct e as [v' sexpr'] eqn:E_e.
      destruct (YULVariable.eqb v' v) eqn:E_eqb_v'_v.
      + injection H_search as H_hl H_sexpr H_tl.
        rewrite <- H_hl.
        intro sexpr0.
        intro H_contra.
        destruct H_contra.
      + destruct (search_renamings_split l' v) as [[hl' [sexpr''|]] tl'] eqn:E_search_rec; try discriminate.        
        injection H_search as H_hl H_sexpr H_tl.
        rewrite <- H_hl.
        subst sexpr''.
        intros sexpr0.
        intro H_contra.
        simpl in  H_contra.
        destruct H_contra as [H_contra | H_contra].
        * injection H_contra as H_v'_v _.
          rewrite Nat.eqb_neq in E_eqb_v'_v.
          contradiction.
        * contradiction (IHl' hl' tl' v sexpr E_search_rec sexpr0).
  Qed.
    
    
  Lemma renaming_split_false:
    forall (l hl tl: YULVariableMapD.t) (v: YULVariable.t),
      search_renamings_split l v = (hl, None, tl) ->
      forall (hl tl: YULVariableMapD.t) (sexpr: SimpleExprD.t),
        l <> hl++(v, sexpr)::tl.
  Proof.
    induction l as [|e l' IHl'].
    - intros hl tl v H_search.
      intros hl' tl' sexpr H_contra.
      apply len_eq in H_contra.
      rewrite length_app in H_contra.
      simpl in H_contra.
      rewrite <- plus_n_Sm in H_contra.
      discriminate H_contra.
    - intros hl tl v H_search.
      intros hl' tl' sexpr H_contra.      
      simpl in H_search.
      destruct e as [v' sexpr'].
      destruct (YULVariable.eqb v' v) eqn:E_eqb_v'_v'; try discriminate.      
      destruct (search_renamings_split l' v) as [[hl'' [sexpr''|]] tl''] eqn:E_search_rec; try discriminate.
      injection H_search as H_hl H_tl. 
      subst hl.
      subst tl.
      destruct hl' as [| e' hl'''].
      + simpl in H_contra.
        injection H_contra as H_v H_sexpr H_l'.
        unfold YULVariable.eqb in E_eqb_v'_v'.
        rewrite Nat.eqb_neq in E_eqb_v'_v'.
        contradiction.
      + simpl in H_contra.
        injection H_contra as H_e' H_l'.
        contradiction (IHl' hl'' tl'' v E_search_rec hl''' tl' sexpr).
  Qed.

  Lemma renaming_split_false_not_In:
    forall (l hl tl: YULVariableMapD.t) (v: YULVariable.t),
      search_renamings_split l v = (hl, None, tl) ->
      forall sexpr, ~ List.In (v,sexpr) l.
  Proof.
    induction l as [|e l' IHl'].
    - intros hl tl v H_search.
      intros sexpr H_contra.
      destruct H_contra.
    - intros hl tl v H_search.
      intros sexpr H_contra.
      simpl in H_search.
      destruct e as [v' sexpr'].
      destruct (YULVariable.eqb v' v) eqn:E_eqb_v'_v; try discriminate.
      destruct (search_renamings_split l' v) as [[hl'' [sexpr''|]] tl''] eqn:E_search_rec; try discriminate.
      injection H_search as H_hl H_tl.
      simpl in  H_contra.
      destruct H_contra as [H_contra | H_contra].
      * injection H_contra as H_v'_v _.
        unfold YULVariable.eqb in E_eqb_v'_v.
        rewrite Nat.eqb_neq in E_eqb_v'_v.
        contradiction.
      * contradiction (IHl' hl'' tl'' v E_search_rec sexpr).
  Qed.

  Lemma renaming_split:
    forall l v,
      (exists hl tl sexpr, (l = hl++(v, sexpr)::tl)/\ forall sexpr, ~ List.In (v,sexpr) hl)
      \/
      ( (forall (hl tl: YULVariableMapD.t) (sexpr: SimpleExprD.t), l <> hl++(v, sexpr)::tl) /\ forall sexpr, ~ List.In (v,sexpr) l).
  Proof.
    intros l v.
    destruct (search_renamings_split l v) as [[hl [sexpr|]] tl] eqn:E_search.
    - pose proof (renaming_split_true l hl tl v sexpr E_search) as H1.
      pose proof (renaming_split_true_not_In l hl tl v sexpr E_search) as H2.
      left.
      exists hl.
      exists tl.
      exists sexpr.
      split.
      + apply H1.
      + apply H2.
    - pose proof (renaming_split_false l hl tl v E_search) as H1.
      pose proof (renaming_split_false_not_In l hl tl v E_search) as H2.
      right.
      split.
      + apply H1.
      + apply H2.
  Qed.      


  Lemma apply_renamings_app:
    forall l l1 l2 a,
      l1++l2 = l ->
      (forall v,
          VariableAssignmentD.apply_renamings a l v =
            VariableAssignmentD.apply_renamings (VariableAssignmentD.apply_renamings a l1) l2 v).
  Proof.
    induction l as [|e l' IHl'].
    - simpl.
      intros l1 l2 a H_app v.
      apply app_eq_nil in H_app.
      destruct H_app as [H_l1 H_l2].
      rewrite H_l1.
      rewrite H_l2.
      simpl.
      reflexivity.
    - intros l1 l2 a H_app v.
      destruct l1 as [|e' l1'] eqn:E_l1.
      + simpl in H_app.
        rewrite H_app.
        simpl.
        reflexivity.
      + simpl in H_app.
        injection H_app as H_e' H_l'.
        rewrite H_e'.
        simpl.
        destruct e as [dest origin].
        remember (VariableAssignmentD.assign a dest (VariableAssignmentD.get_se a origin)) as a' eqn:E_a'.
        apply (IHl' l1' l2 a' H_l' ).
  Qed.

        
  Lemma apply_renamings_snd:
    forall l v assign1 assign2,
      (forall v', v'<>v -> assign1 v' = assign2 v') ->
      (forall v', ~List.In (v',(inl v)) l) ->
      (forall v',
          v'<>v ->
          VariableAssignmentD.apply_renamings assign1 l v'=
            VariableAssignmentD.apply_renamings assign2 l v').
  Proof.
    induction l as [ | e l'].
    - intros v assign1 assign2 H_equiv_up_to_v H_not_in.
      intros v' H_neq_v'_v.
      simpl.
      apply H_equiv_up_to_v.
      apply H_neq_v'_v.
    - intros v assign1 assign2 H_equiv_up_to_v H_not_in.
      intros v' H_neq_v'_v.
      simpl.
      destruct e as [dest origin] eqn:E_e.
      
      destruct origin as [origin_var | origin_val] eqn:E_origin.
      + pose proof (H_not_in dest) as H_not_in_dest.
        simpl in H_not_in_dest.
        apply Decidable.not_or in H_not_in_dest.
        destruct H_not_in_dest as [H_not_in_dest_1 H_not_in_dest_2].
        assert(H_origin_var_neq_v: origin_var <> v). congruence.
        simpl.
        rewrite (H_equiv_up_to_v origin_var H_origin_var_neq_v).
        
        pose proof (assign_preserves_equiv_up_to_v assign1 assign2 v dest (assign2 origin_var) H_equiv_up_to_v) as H_equiv_new_assign.
        unfold VariableAssignmentD.get in H_equiv_new_assign.

        simpl in H_not_in.
        rewrite forall_not_or_dist in H_not_in.
        destruct H_not_in as [H_not_in_1 H_not_in_2].
        
        apply (IHl' v (SmallStepD.VariableAssignmentD.assign assign1 dest (assign2 origin_var)) (SmallStepD.VariableAssignmentD.assign assign2 dest (assign2 origin_var)) H_equiv_new_assign H_not_in_2 v' H_neq_v'_v).
      + simpl.
        pose proof (assign_preserves_equiv_up_to_v assign1 assign2 v dest origin_val H_equiv_up_to_v) as H_equiv_new_assign.
        simpl in H_not_in.
        rewrite forall_not_or_dist in H_not_in.
        destruct H_not_in as [H_not_in_1 H_not_in_2].
        
        apply (IHl' v (SmallStepD.VariableAssignmentD.assign assign1 dest origin_val) (SmallStepD.VariableAssignmentD.assign assign2 dest origin_val) H_equiv_new_assign H_not_in_2 v' H_neq_v'_v).
  Qed.

  
   
  Lemma live_at_handle_block_finish_snd:   
    forall (p: SmartContractD.t) (i: nat) (fname: FunctionName.t) (bid: BlockID.t) (b: BlockD.t) (pc: nat) (s: VarSet.t),
      SmartContractD.get_block p fname bid = Some b ->
      live_at_pc' p fname bid pc s ->
      forall  (st1 st2 st1': StateD.t) (v: YULVariable.t),
        equiv_states_up_to_i_v p i fname bid pc v st1 st2 ->
        SmallStepD.get_next_instruction st1 p = None ->
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
    intros p i fname bid b pc s H_b_exists H_live_at_pc st1 st2 st1' v H_equiv_st1_st2 H_get_instr H_handle_block_finish H_not_In_v_s.
    assert (H_equiv_st1_st2' := H_equiv_st1_st2).
    unfold equiv_states_up_to_i_v in H_equiv_st1_st2'.
    destruct H_equiv_st1_st2' as [H_lt_i [H_len_call_stack [H_status [H_dialect [hl [tl [sf1 [sf2 [H_split_i_st1 [H_split_i_st2 H_equiv_sf1_sf2]]]]]]]]]].

    unfold split_at_i in H_split_i_st1.
    destruct H_split_i_st1 as [H_lt_i_st1 [H_call_stack_st1 H_len_tl_st1]].
    
    unfold split_at_i in H_split_i_st2.
    destruct H_split_i_st2 as [H_lt_i_st2 [H_call_stack_st2 H_len_tl_st2]].

    assert (H_equiv_sf1_sf2' := H_equiv_sf1_sf2).
    unfold equiv_stack_frames_up_to_v in H_equiv_sf1_sf2'.
    destruct H_equiv_sf1_sf2' as [H_fname_sf1 [H_bid_sf1 [H_pc_sf1 [H_fname_sf2 [H_bid_sf2 [H_pc_sf2 H_equiv_assign_sf1_sf2]]]]]]. 
    
    destruct hl as [|top_sf hl'] eqn:E_hl.

    (* the case where the top stack frame is the one with different values for v *)
    - simpl in H_call_stack_st1.
      simpl in H_call_stack_st2.

      unfold SmallStepD.handle_block_finish in H_handle_block_finish.
      rewrite H_call_stack_st1 in H_handle_block_finish.
      rewrite H_fname_sf1 in H_handle_block_finish.
      rewrite H_bid_sf1 in H_handle_block_finish.
      rewrite H_b_exists in H_handle_block_finish.

      unfold SmallStepD.handle_block_finish.
      rewrite H_call_stack_st2.
      rewrite H_fname_sf2.
      rewrite H_bid_sf2.
      rewrite H_b_exists.

      destruct (BlockD.exit_info b) as [cond_var target_if_true target_if_false|next_bid|rs|] eqn:E_b_exit_info.

      
      (* condition block *)
      +  assert( H_live_at_pc' :=  H_live_at_pc).

         destruct H_live_at_pc' as [fname bid b0 pc s sout H_b0_exists H_live_out H_pc_at_end H_sout | fname bid b0 pc s sout instr' H_b0_exists H_live_at_S_pc H_lt_pc' H_get_instr' H_sout].

         * rewrite H_b_exists in H_b0_exists.
           injection H_b0_exists as H_b0_exists.
           subst b0.

           assert(H_cv_neq_v: cond_var <> v).
           {
             unfold add_jump_var_if_applicable in H_sout.
             rewrite E_b_exit_info in H_sout.
             pose proof (not_In_preserves_eq  sout (VarSet.add cond_var s) v H_sout H_not_In_v_s) as H_not_In_v_add_cvar.
             rewrite VarSet.add_spec in H_not_In_v_add_cvar.
             apply Decidable.not_or in H_not_In_v_add_cvar as [H_v_neq_cvar _].
             congruence.
           }.
           
           rewrite <- (H_equiv_assign_sf1_sf2 cond_var H_cv_neq_v).

           destruct (D.is_true_value (VariableAssignmentD.get (StackFrameD.variable_assignments sf1) cond_var)) eqn:E_cond_var_value.

           (* the condition is true *)
           ** destruct (SmallStepD.SmartContractD.get_block p fname target_if_true) as [next_b|] eqn:E_next_b.

              (* block found *)
              *** destruct H_live_out as [ fname bid b0 rs' sout0 H_b0_exists H_is_ret H_sout0| fname bid b0 sout0 H_b0_exists H_is_termin | fname bid next_bid' b0 next_b0 s' sout0 H_b0_exists H_is_jump H_live_in_next_pc H_next_b0_exists H_sout0 | fname bid  next_bid_if_true next_bid_if_false cvar b0 next_b0_if_true next_b0_if_false s1' s2' sout0 H_b0_exists H_is_cjump H_live_at_pc_if_true H_live_at_pc_if_false H_next_b0_if_true H_next_b0_if_false H_sout0].
 
                  **** rewrite H_b_exists in H_b0_exists.
                       injection H_b0_exists as H_b0_exists.
                       subst b0.
                       unfold BlockD.is_return_block in H_is_ret.
                       rewrite E_b_exit_info in H_is_ret.
                       discriminate H_is_ret.
                  **** rewrite H_b_exists in H_b0_exists.
                       injection H_b0_exists as H_b0_exists.
                       subst b0.
                       unfold BlockD.is_terminated_block in H_is_termin.
                       rewrite E_b_exit_info in H_is_termin.
                       discriminate H_is_termin.
                       
                  **** rewrite H_b_exists in H_b0_exists.
                       injection H_b0_exists as H_b0_exists.
                       subst b0.
                       unfold BlockD.is_jump_block in H_is_jump.
                       rewrite E_b_exit_info in H_is_jump.
                       discriminate H_is_jump.

                  **** rewrite H_b_exists in H_b0_exists.
                       injection H_b0_exists as H_b0_exists.
                       subst b0.

                       unfold BlockD.is_cond_jump_block in H_is_cjump.
                       rewrite E_b_exit_info in H_is_cjump.
                       injection H_is_cjump as H_cond_var H_target_if_true H_target_if_false.
                       subst cvar.
                       subst target_if_true.
                       subst target_if_false.

                       remember next_bid_if_true as next_bid eqn:E_next_bid.

                       rewrite E_next_b in H_next_b0_if_true.
                       injection H_next_b0_if_true as  H_next_b0_if_true.
                       subst next_b0_if_true.
                                               
                       unfold add_jump_var_if_applicable in H_sout.
                       rewrite E_b_exit_info in H_sout.
                 
                       rewrite  (add_preserves_equal sout0 (VarSet.union (apply_inv_phi (BlockD.phi_function next_b bid) s1') (apply_inv_phi (BlockD.phi_function next_b0_if_false bid) s2')) cond_var H_sout0) in H_sout.

                       unfold SmallStepD.apply_renamings in H_handle_block_finish.
                       unfold SmallStepD.apply_renamings.

                       remember (SmallStepD.get_renaming_sexpr (SmallStepD.SmartContractD.BlockD.phi_function next_b bid)) as phi_invars eqn:E_phi_invars.

                       remember (SmallStepD.get_renaming_var (SmallStepD.SmartContractD.BlockD.phi_function next_b bid)) as phi_outvars eqn:E_phi_outvars.

                       assert (H_not_In_v_input: ~ In (inl v) phi_invars).
                       {
                         pose proof (not_In_preserves_eq sout (VarSet.add cond_var (VarSet.union (apply_inv_phi (BlockD.phi_function next_b bid) s1') (apply_inv_phi (BlockD.phi_function next_b0_if_false bid) s2'))) v H_sout H_not_In_v_s) as H_v_not_in_inv.
                         unfold apply_inv_phi in H_v_not_in_inv.
                         rewrite <- E_phi_invars in H_v_not_in_inv.
                         rewrite <- E_phi_outvars in H_v_not_in_inv.
                         rewrite VarSet.add_spec in H_v_not_in_inv.
                         apply Decidable.not_or in H_v_not_in_inv.
                         destruct H_v_not_in_inv as [_ H_v_not_in_inv].
                         rewrite VarSet.union_spec in H_v_not_in_inv.
                         apply Decidable.not_or in H_v_not_in_inv.
                         destruct H_v_not_in_inv as [H_v_not_in_inv _].
                         rewrite VarSet.union_spec in H_v_not_in_inv.
                         apply Decidable.not_or in H_v_not_in_inv.
                         destruct H_v_not_in_inv as [_ H_v_not_in_inv].
                         rewrite <- list_to_set_spec in  H_v_not_in_inv.
                         rewrite <- extract_yul_vars_spec in H_v_not_in_inv.
                         apply H_v_not_in_inv.
                       }.

                       rewrite <- (eval_sexpr_snd phi_invars fname bid pc v sf1 sf2 H_equiv_sf1_sf2 H_not_In_v_input).

                       destruct (SmallStepD.VariableAssignmentD.assign_all (SmallStepD.StackFrameD.variable_assignments sf1) phi_outvars (SmallStepD.eval_sexpr phi_invars sf1)) as [var_assignments_1|] eqn:E_assign_all_1.

                       ***** pose proof (assign_all_some phi_outvars (SmallStepD.eval_sexpr phi_invars sf1) (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) var_assignments_1 E_assign_all_1) as [var_assignments_2 E_assign_all_2].
                       rewrite E_assign_all_2.
                       
                       rewrite <- live_at_pc_zero_eq_live_in in H_live_at_pc_if_true.
                       rewrite (live_at_pc'_0_equiv_live_at_pc_0 p fname next_bid next_b s1' E_next_b) in H_live_at_pc_if_true.

                       remember {|
                                  Liveness_snd.StateD.call_stack :=
                                    {|
                                      Liveness_snd.StackFrameD.function_name := fname;
                                      Liveness_snd.StackFrameD.variable_assignments := var_assignments_2;
                                      Liveness_snd.StackFrameD.curr_block_id := next_bid;
                                      Liveness_snd.StackFrameD.pc := 0
                                    |} :: tl;
                          Liveness_snd.StateD.status := Status.Running;
                          Liveness_snd.StateD.dialect_state := SmallStepD.StateD.dialect_state st2
                        |} as st2' eqn:E_st2'.

                       exists st2'.
                       exists next_bid.
                       exists next_b.
                       exists 0%nat.
                       exists s1'.
                       repeat split.
                       ****** apply E_next_b.
                       ****** (* split on wether v is in the phi_outvars *)
                            pose proof (varlist_in_dec phi_outvars v) as H_v_output.
                      
                            destruct H_v_output as [H_v_in_output | H_v_not_in_output].
                            ******** right.
                                     rewrite <- (assign_all_preserves_eq_up_to_eq phi_outvars (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) v (SmallStepD.eval_sexpr phi_invars sf1) var_assignments_1 var_assignments_2 H_v_in_output H_equiv_assign_sf1_sf2 E_assign_all_1 E_assign_all_2) in E_st2'.
                            
                                     rewrite E_st2'.
                                     rewrite <- H_handle_block_finish.
                                     rewrite H_dialect.
                                     reflexivity.
                                     
                            ******** left.
                                     repeat split.
                                     ********* rewrite <- H_handle_block_finish.
                                               simpl.
                                               rewrite H_call_stack_st1 in H_lt_i.
                                               simpl in H_lt_i.
                                               apply H_lt_i.
                                     ********* rewrite <- H_handle_block_finish.
                                               rewrite E_st2'.
                                               simpl.
                                               reflexivity.
                                     ********* rewrite <- H_handle_block_finish.
                                               rewrite E_st2'.
                                               simpl.
                                               reflexivity.
                                     ********* rewrite <- H_handle_block_finish.
                                               rewrite E_st2'.
                                               simpl.
                                               apply H_dialect.
                                     ********* exists [].
                                               exists tl.
                                               exists {|
                                                   Liveness_snd.StackFrameD.function_name := fname;
                                                   Liveness_snd.StackFrameD.variable_assignments := var_assignments_1;
                                                   Liveness_snd.StackFrameD.curr_block_id := next_bid;
                                                   Liveness_snd.StackFrameD.pc := 0
                                                 |}.
                                               exists {|
                                                   Liveness_snd.StackFrameD.function_name := fname;
                                                   Liveness_snd.StackFrameD.variable_assignments := var_assignments_2;
                                                   Liveness_snd.StackFrameD.curr_block_id := next_bid;
                                                   Liveness_snd.StackFrameD.pc := 0
                                                 |}.
                                               repeat split.
                                               ********** rewrite <- H_handle_block_finish.
                                                          simpl.
                                                          rewrite H_call_stack_st1 in H_lt_i.
                                                          simpl in H_lt_i.
                                                          apply H_lt_i.
                                               ********** rewrite <- H_handle_block_finish.
                                                          simpl.     
                                                          reflexivity.
                                               ********** apply H_len_tl_st1.
                                               ********** rewrite E_st2'.
                                                          simpl.
                                                          rewrite H_call_stack_st1 in H_lt_i.
                                                          simpl in H_lt_i.
                                                          apply H_lt_i.
                                               ********** rewrite E_st2'.
                                                          simpl.
                                                          reflexivity.
                                               ********** apply H_len_tl_st2.
                                               ********** simpl.
                                                          apply (assign_all_preserves_eq_up_to phi_outvars (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) v (SmallStepD.eval_sexpr phi_invars sf1) var_assignments_1 var_assignments_2 H_v_not_in_output H_equiv_assign_sf1_sf2 E_assign_all_1 E_assign_all_2).

                                   ********* apply H_live_at_pc_if_true.
                                   ********* pose proof (not_In_preserves_eq sout (VarSet.add cond_var (VarSet.union (apply_inv_phi (BlockD.phi_function next_b bid) s1') (apply_inv_phi (BlockD.phi_function next_b0_if_false bid) s2'))) v H_sout H_not_In_v_s) as H_not_In_v_s'.
                                           unfold apply_inv_phi in H_not_In_v_s'.
                                           rewrite <- E_phi_invars in H_not_In_v_s'.
                                           rewrite <- E_phi_outvars in H_not_In_v_s'.
                                           rewrite VarSet.add_spec in H_not_In_v_s'.
                                           apply Decidable.not_or in H_not_In_v_s' as [_ H_not_In_v_s'].
                                           rewrite VarSet.union_spec in H_not_In_v_s'.
                                           apply Decidable.not_or in H_not_In_v_s' as [H_not_In_v_s' _].
                                           rewrite VarSet.union_spec in H_not_In_v_s'.
                                           apply Decidable.not_or in H_not_In_v_s' as [H_not_In_v_s' _].
                                           rewrite VarSet.diff_spec in H_not_In_v_s'.
                                           apply Decidable.not_and in H_not_In_v_s' as [H_not_In_v_s' | H_not_In_v_s' ].
                                           ********** apply H_not_In_v_s'.
                                           ********** apply Decidable.not_not in H_not_In_v_s'.
                                                      rewrite <- list_to_set_spec in H_not_In_v_s'.
                                                      contradiction H_not_In_v_s'.
                                                      apply varset_in_dec.
                                           ********** apply varset_in_dec.

                       ****** (* split on wether v is in the phi_outvars *)
                              pose proof (varlist_in_dec phi_outvars v) as H_v_output.
                      
                              destruct H_v_output as [H_v_in_output | H_v_not_in_output].

                              ******* rewrite <- (assign_all_preserves_eq_up_to_eq phi_outvars (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) v (SmallStepD.eval_sexpr phi_invars sf1) var_assignments_1 var_assignments_2 H_v_in_output H_equiv_assign_sf1_sf2 E_assign_all_1 E_assign_all_2) in E_st2'.
                            
                                      rewrite E_st2'.
                                      rewrite <- H_handle_block_finish.
                                      rewrite H_dialect.
                                      unfold equiv_vars_in_top_frame.
                                      simpl.
                                      repeat split; try reflexivity.

                             ******* rewrite <- H_handle_block_finish.
                                     rewrite E_st2'.
                                     unfold equiv_vars_in_top_frame.
                                     simpl.
                                     repeat split; try reflexivity.
                                     intros v0 s0 H_accessed_vars H_In_v0_s0.


                                   assert(H_not_v_In_s'': ~ VarSet.In v s1').
                                   {
                                     pose proof (not_In_preserves_eq sout (VarSet.add cond_var (VarSet.union (apply_inv_phi (BlockD.phi_function next_b bid) s1') (apply_inv_phi (BlockD.phi_function next_b0_if_false bid) s2'))) v H_sout H_not_In_v_s) as H_not_In_v_s'.
                                     unfold apply_inv_phi in H_not_In_v_s'.
                                     rewrite <- E_phi_invars in H_not_In_v_s'.
                                     rewrite <- E_phi_outvars in H_not_In_v_s'.
                                     rewrite VarSet.add_spec in H_not_In_v_s'.
                                     apply Decidable.not_or in H_not_In_v_s' as [_ H_not_In_v_s'].
                                     rewrite VarSet.union_spec in H_not_In_v_s'.
                                     apply Decidable.not_or in H_not_In_v_s' as [H_not_In_v_s' _].
                                     rewrite VarSet.union_spec in H_not_In_v_s'.
                                     apply Decidable.not_or in H_not_In_v_s' as [H_not_In_v_s' _].
                                     rewrite VarSet.diff_spec in H_not_In_v_s'.
                                     apply Decidable.not_and in H_not_In_v_s' as [H_not_In_v_s' | H_not_In_v_s' ].
                                     ******** apply H_not_In_v_s'.
                                     ******** apply Decidable.not_not in H_not_In_v_s'.
                                     rewrite <- list_to_set_spec in H_not_In_v_s'.
                                     contradiction H_not_In_v_s'.
                                     apply varset_in_dec.
                                     ******** apply varset_in_dec.
                                   }.


                                   apply (assign_all_preserves_eq_up_to phi_outvars (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) v (SmallStepD.eval_sexpr phi_invars sf1) var_assignments_1 var_assignments_2 H_v_not_in_output H_equiv_assign_sf1_sf2 E_assign_all_1 E_assign_all_2).

                                   apply (accessed_var_instr_neq_v p fname next_bid next_b 0%nat s0 v0 s1' v E_next_b H_live_at_pc_if_true H_not_v_In_s'' H_accessed_vars H_In_v0_s0).

                       ***** rewrite (assign_all_none phi_outvars (SmallStepD.eval_sexpr phi_invars sf1) (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) E_assign_all_1).

                             remember (SmallStepD.StateD.set_status st2 (Status.Error "Error while applying phi-function")) as st2' eqn:E_st2'.

                             exists st2'.
                             exists bid.
                             exists b.
                             exists pc.
                             exists sout.
                             repeat split.
                             ****** apply H_b_exists.
                             ****** left.
                                    repeat split.
                                    ******* rewrite <- H_handle_block_finish.
                                            simpl.
                                            apply H_lt_i.
                                   ******* rewrite <- H_handle_block_finish.
                                           rewrite E_st2'.
                                           simpl.
                                           apply H_len_call_stack.
                                   ******* rewrite <- H_handle_block_finish.
                                           rewrite E_st2'.
                                           simpl.
                                           reflexivity.
                                   ******* rewrite <- H_handle_block_finish.
                                           rewrite E_st2'.
                                           simpl.
                                           apply H_dialect.
                                   ******* exists [].
                                           exists tl.
                                           exists sf1.
                                           exists sf2.
                                           repeat split.
                                           ******** rewrite <- H_handle_block_finish.
                                                    simpl.
                                                    apply H_lt_i.
                                           ******** rewrite <- H_handle_block_finish.
                                                    simpl.
                                                    apply H_call_stack_st1.
                                           ******** apply H_len_tl_st1.
                                           ******** rewrite E_st2'.
                                                    simpl.
                                                    rewrite H_call_stack_st1 in H_lt_i.
                                                    simpl in H_lt_i.
                                                    rewrite H_call_stack_st2.
                                                    simpl.
                                                    apply H_lt_i.
                                           ******** rewrite E_st2'.
                                                    simpl.
                                                    apply H_call_stack_st2.
                                           ******** apply H_len_tl_st2.
                                           ******** apply H_fname_sf1.
                                           ******** apply H_bid_sf1.
                                           ******** apply H_pc_sf1.
                                           ******** apply H_fname_sf2.
                                           ******** apply H_bid_sf2.
                                           ******** apply H_pc_sf2.
                                           ******** apply H_equiv_assign_sf1_sf2.
                                   ******* apply H_live_at_pc.
                                   ******* apply H_not_In_v_s.
                             ****** rewrite <- H_handle_block_finish.
                                    rewrite E_st2'.
                                    unfold equiv_vars_in_top_frame.
                                    simpl.
                                    rewrite H_call_stack_st1.
                                    rewrite H_call_stack_st2.
                                    repeat split.
                                    ******* rewrite H_fname_sf1. rewrite H_fname_sf2. reflexivity.
                                    ******* rewrite H_bid_sf1. rewrite H_bid_sf2. reflexivity.
                                    ******* rewrite H_pc_sf1. rewrite H_pc_sf2. reflexivity.
                                    ******* intros v0 s0 H_accessed_vars H_In_v0_s0.
                                            pose proof (accessed_var_instr_neq_v p fname bid b pc s0 v0 sout v H_b_exists H_live_at_pc H_not_In_v_s H_accessed_vars H_In_v0_s0) as H_v0_neq_v.
                                            apply (H_equiv_assign_sf1_sf2 v0 H_v0_neq_v).

              (* block not found *)
              *** remember (SmallStepD.StateD.set_status st2 (Status.Error "Target block not found in the smart contract")) as st2' eqn:H_st2'.
                  exists st2'.
                  exists bid.
                  exists b.
                  exists pc.
                  exists sout.
                  repeat split.
                  **** apply H_b_exists.
                  **** left.
                       repeat split.
                       ***** rewrite <- H_handle_block_finish.
                             simpl.
                             apply H_lt_i.
                       ***** rewrite <- H_handle_block_finish.
                             rewrite H_st2'.
                             simpl.
                             apply H_len_call_stack.
                       ***** rewrite <- H_handle_block_finish.
                             rewrite H_st2'.
                             simpl.
                             reflexivity.
                       ***** rewrite <- H_handle_block_finish.
                             rewrite H_st2'.
                             simpl.
                             apply H_dialect.
                       ***** exists [].
                             exists tl.
                             exists sf1.
                             exists sf2.
                             repeat split.
                             ****** rewrite <- H_handle_block_finish.
                                    simpl.
                                    apply H_lt_i.
                             ****** rewrite <- H_handle_block_finish.
                                    simpl.
                                    apply H_call_stack_st1.
                             ****** apply H_len_tl_st1.
                             ****** rewrite H_st2'.
                                    simpl.
                                    rewrite H_call_stack_st2.
                                    simpl.
                                    rewrite H_call_stack_st1 in H_lt_i.
                                    simpl in H_lt_i.
                                    apply H_lt_i.
                            ****** rewrite H_st2'.
                                   simpl.
                                   apply H_call_stack_st2.
                            ****** apply H_len_tl_st2.
                            ****** apply H_fname_sf1.
                            ****** apply H_bid_sf1.
                            ****** apply H_pc_sf1.
                            ****** apply H_fname_sf2.
                            ****** apply H_bid_sf2.
                            ****** apply H_pc_sf2.
                            ****** apply H_equiv_assign_sf1_sf2.
                       ***** apply H_live_at_pc.
                       ***** apply H_not_In_v_s.
                  **** rewrite <- H_handle_block_finish.
                       rewrite H_st2'.
                       unfold equiv_vars_in_top_frame.
                       simpl.
                       rewrite H_call_stack_st1.
                       rewrite H_call_stack_st2.
                       repeat split.
                       ***** rewrite H_fname_sf1. rewrite H_fname_sf2. reflexivity.
                       ***** rewrite H_bid_sf1. rewrite H_bid_sf2. reflexivity.
                       ***** rewrite H_pc_sf1. rewrite H_pc_sf2. reflexivity.
                       ***** intros v0 s0 H_accessed_vars H_In_v0_s0.
                             pose proof (accessed_var_instr_neq_v p fname bid b pc s0 v0 sout v H_b_exists H_live_at_pc H_not_In_v_s H_accessed_vars H_In_v0_s0) as H_v0_neq_v.
                             apply (H_equiv_assign_sf1_sf2 v0 H_v0_neq_v).

           (* the condition is false *)
           ** destruct (SmallStepD.SmartContractD.get_block p fname target_if_false) as [next_b|] eqn:E_next_b.

              (* block found *)
              *** destruct H_live_out as [ fname bid b0 rs' sout0 H_b0_exists H_is_ret H_sout0| fname bid b0 sout0 H_b0_exists H_is_termin | fname bid next_bid' b0 next_b0 s' sout0 H_b0_exists H_is_jump H_live_in_next_pc H_next_b0_exists H_sout0 | fname bid  next_bid_if_true next_bid_if_false cvar b0 next_b0_if_true next_b0_if_false s1' s2' sout0 H_b0_exists H_is_cjump H_live_at_pc_if_true H_live_at_pc_if_false H_next_b0_if_true H_next_b0_if_false H_sout0].
 
                  **** rewrite H_b_exists in H_b0_exists.
                       injection H_b0_exists as H_b0_exists.
                       subst b0.
                       unfold BlockD.is_return_block in H_is_ret.
                       rewrite E_b_exit_info in H_is_ret.
                       discriminate H_is_ret.
                  **** rewrite H_b_exists in H_b0_exists.
                       injection H_b0_exists as H_b0_exists.
                       subst b0.
                       unfold BlockD.is_terminated_block in H_is_termin.
                       rewrite E_b_exit_info in H_is_termin.
                       discriminate H_is_termin.
                       
                  **** rewrite H_b_exists in H_b0_exists.
                       injection H_b0_exists as H_b0_exists.
                       subst b0.
                       unfold BlockD.is_jump_block in H_is_jump.
                       rewrite E_b_exit_info in H_is_jump.
                       discriminate H_is_jump.

                  **** rewrite H_b_exists in H_b0_exists.
                       injection H_b0_exists as H_b0_exists.
                       subst b0.

                       unfold BlockD.is_cond_jump_block in H_is_cjump.
                       rewrite E_b_exit_info in H_is_cjump.
                       injection H_is_cjump as H_cond_var H_target_if_true H_target_if_false.
                       subst cvar.
                       subst target_if_true.
                       subst target_if_false.

                       remember next_bid_if_false as next_bid eqn:E_next_bid.

                       rewrite E_next_b in H_next_b0_if_false.
                       injection H_next_b0_if_false as  H_next_b0_if_false.
                       subst next_b0_if_false.
                                               
                       unfold add_jump_var_if_applicable in H_sout.
                       rewrite E_b_exit_info in H_sout.
                 
                       rewrite  (add_preserves_equal sout0 (VarSet.union (apply_inv_phi (BlockD.phi_function next_b0_if_true bid) s1') (apply_inv_phi (BlockD.phi_function next_b bid) s2')) cond_var H_sout0) in H_sout.

                       unfold SmallStepD.apply_renamings in H_handle_block_finish.
                       unfold SmallStepD.apply_renamings.

                       remember (SmallStepD.get_renaming_sexpr (SmallStepD.SmartContractD.BlockD.phi_function next_b bid)) as phi_invars eqn:E_phi_invars.

                       remember (SmallStepD.get_renaming_var (SmallStepD.SmartContractD.BlockD.phi_function next_b bid)) as phi_outvars eqn:E_phi_outvars.

                       assert (H_not_In_v_input: ~ In (inl v) phi_invars).
                       {
                         pose proof (not_In_preserves_eq sout (VarSet.add cond_var (VarSet.union (apply_inv_phi (BlockD.phi_function next_b0_if_true bid) s1') (apply_inv_phi (BlockD.phi_function next_b bid) s2'))) v H_sout H_not_In_v_s) as H_v_not_in_inv.
                         unfold apply_inv_phi in H_v_not_in_inv.
                         rewrite <- E_phi_invars in H_v_not_in_inv.
                         rewrite <- E_phi_outvars in H_v_not_in_inv.
                         rewrite VarSet.add_spec in H_v_not_in_inv.
                         apply Decidable.not_or in H_v_not_in_inv.
                         destruct H_v_not_in_inv as [_ H_v_not_in_inv].
                         rewrite VarSet.union_spec in H_v_not_in_inv.
                         apply Decidable.not_or in H_v_not_in_inv.
                         destruct H_v_not_in_inv as [_ H_v_not_in_inv].
                         rewrite VarSet.union_spec in H_v_not_in_inv.
                         apply Decidable.not_or in H_v_not_in_inv.
                         destruct H_v_not_in_inv as [_ H_v_not_in_inv].
                         rewrite <- list_to_set_spec in  H_v_not_in_inv.
                         rewrite <- extract_yul_vars_spec in H_v_not_in_inv.
                         apply H_v_not_in_inv.
                       }.

                       rewrite <- (eval_sexpr_snd phi_invars fname bid pc v sf1 sf2 H_equiv_sf1_sf2 H_not_In_v_input).

                       destruct (SmallStepD.VariableAssignmentD.assign_all (SmallStepD.StackFrameD.variable_assignments sf1) phi_outvars (SmallStepD.eval_sexpr phi_invars sf1)) as [var_assignments_1|] eqn:E_assign_all_1.

                       ***** pose proof (assign_all_some phi_outvars (SmallStepD.eval_sexpr phi_invars sf1) (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) var_assignments_1 E_assign_all_1) as [var_assignments_2 E_assign_all_2].
                              rewrite E_assign_all_2.
                       
                              rewrite <- live_at_pc_zero_eq_live_in in H_live_at_pc_if_false.
                              rewrite (live_at_pc'_0_equiv_live_at_pc_0 p fname next_bid next_b s2' E_next_b) in H_live_at_pc_if_false.

                              remember {|
                                  Liveness_snd.StateD.call_stack :=
                                    {|
                                      Liveness_snd.StackFrameD.function_name := fname;
                                      Liveness_snd.StackFrameD.variable_assignments := var_assignments_2;
                                      Liveness_snd.StackFrameD.curr_block_id := next_bid;
                                      Liveness_snd.StackFrameD.pc := 0
                                    |} :: tl;
                                  Liveness_snd.StateD.status := Status.Running;
                                  Liveness_snd.StateD.dialect_state := SmallStepD.StateD.dialect_state st2
                                |} as st2' eqn:E_st2'.
                              
                              exists st2'.
                              exists next_bid.
                       exists next_b.
                       exists 0%nat.
                       exists s2'.
                       repeat split.
                       ****** apply E_next_b.
                       ****** (* split on wether v is in the phi_outvars *)
                            pose proof (varlist_in_dec phi_outvars v) as H_v_output.
                      
                            destruct H_v_output as [H_v_in_output | H_v_not_in_output].
                            ******** right.
                                     rewrite <- (assign_all_preserves_eq_up_to_eq phi_outvars (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) v (SmallStepD.eval_sexpr phi_invars sf1) var_assignments_1 var_assignments_2 H_v_in_output H_equiv_assign_sf1_sf2 E_assign_all_1 E_assign_all_2) in E_st2'.
                            
                                     rewrite E_st2'.
                                     rewrite <- H_handle_block_finish.
                                     rewrite H_dialect.
                                     reflexivity.
                                     
                            ******** left.
                                     repeat split.
                                     ********* rewrite <- H_handle_block_finish.
                                               simpl.
                                               rewrite H_call_stack_st1 in H_lt_i.
                                               simpl in H_lt_i.
                                               apply H_lt_i.
                                     ********* rewrite <- H_handle_block_finish.
                                               rewrite E_st2'.
                                               simpl.
                                               reflexivity.
                                     ********* rewrite <- H_handle_block_finish.
                                               rewrite E_st2'.
                                               simpl.
                                               reflexivity.
                                     ********* rewrite <- H_handle_block_finish.
                                               rewrite E_st2'.
                                               simpl.
                                               apply H_dialect.
                                     ********* exists [].
                                               exists tl.
                                               exists {|
                                                   Liveness_snd.StackFrameD.function_name := fname;
                                                   Liveness_snd.StackFrameD.variable_assignments := var_assignments_1;
                                                   Liveness_snd.StackFrameD.curr_block_id := next_bid;
                                                   Liveness_snd.StackFrameD.pc := 0
                                                 |}.
                                               exists {|
                                                   Liveness_snd.StackFrameD.function_name := fname;
                                                   Liveness_snd.StackFrameD.variable_assignments := var_assignments_2;
                                                   Liveness_snd.StackFrameD.curr_block_id := next_bid;
                                                   Liveness_snd.StackFrameD.pc := 0
                                                 |}.
                                               repeat split.
                                               ********** rewrite <- H_handle_block_finish.
                                                          simpl.
                                                          rewrite H_call_stack_st1 in H_lt_i.
                                                          simpl in H_lt_i.
                                                          apply H_lt_i.
                                               ********** rewrite <- H_handle_block_finish.
                                                          simpl.     
                                                          reflexivity.
                                               ********** apply H_len_tl_st1.
                                               ********** rewrite E_st2'.
                                                          simpl.
                                                          rewrite H_call_stack_st1 in H_lt_i.
                                                          simpl in H_lt_i.
                                                          apply H_lt_i.
                                               ********** rewrite E_st2'.
                                                          simpl.
                                                          reflexivity.
                                               ********** apply H_len_tl_st2.
                                               ********** simpl.
                                                          apply (assign_all_preserves_eq_up_to phi_outvars (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) v (SmallStepD.eval_sexpr phi_invars sf1) var_assignments_1 var_assignments_2 H_v_not_in_output H_equiv_assign_sf1_sf2 E_assign_all_1 E_assign_all_2).

                                   ********* apply H_live_at_pc_if_false.
                                   ********* pose proof (not_In_preserves_eq sout (VarSet.add cond_var (VarSet.union (apply_inv_phi (BlockD.phi_function next_b0_if_true bid) s1') (apply_inv_phi (BlockD.phi_function next_b bid) s2'))) v H_sout H_not_In_v_s) as H_not_In_v_s'.
                                           unfold apply_inv_phi in H_not_In_v_s'.
                                           rewrite <- E_phi_invars in H_not_In_v_s'.
                                           rewrite <- E_phi_outvars in H_not_In_v_s'.
                                           rewrite VarSet.add_spec in H_not_In_v_s'.
                                           apply Decidable.not_or in H_not_In_v_s' as [_ H_not_In_v_s'].
                                           rewrite VarSet.union_spec in H_not_In_v_s'.
                                           apply Decidable.not_or in H_not_In_v_s' as [_ H_not_In_v_s'].
                                           rewrite VarSet.union_spec in H_not_In_v_s'.
                                           apply Decidable.not_or in H_not_In_v_s' as [H_not_In_v_s' _].
                                           rewrite VarSet.diff_spec in H_not_In_v_s'.
                                           apply Decidable.not_and in H_not_In_v_s' as [H_not_In_v_s' | H_not_In_v_s' ].
                                           ********** apply H_not_In_v_s'.
                                           ********** apply Decidable.not_not in H_not_In_v_s'.
                                                      rewrite <- list_to_set_spec in H_not_In_v_s'.
                                                      contradiction H_not_In_v_s'.
                                                      apply varset_in_dec.
                                           ********** apply varset_in_dec.

                       ****** (* split on wether v is in the phi_outvars *)
                              pose proof (varlist_in_dec phi_outvars v) as H_v_output.
                      
                              destruct H_v_output as [H_v_in_output | H_v_not_in_output].

                              ******* rewrite <- (assign_all_preserves_eq_up_to_eq phi_outvars (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) v (SmallStepD.eval_sexpr phi_invars sf1) var_assignments_1 var_assignments_2 H_v_in_output H_equiv_assign_sf1_sf2 E_assign_all_1 E_assign_all_2) in E_st2'.
                            
                                      rewrite E_st2'.
                                      rewrite <- H_handle_block_finish.
                                      rewrite H_dialect.
                                      unfold equiv_vars_in_top_frame.
                                      simpl.
                                      repeat split; try reflexivity.

                             ******* rewrite <- H_handle_block_finish.
                                     rewrite E_st2'.
                                     unfold equiv_vars_in_top_frame.
                                     simpl.
                                     repeat split; try reflexivity.
                                     intros v0 s0 H_accessed_vars H_In_v0_s0.


                                   assert(H_not_v_In_s'': ~ VarSet.In v s2').
                                   {
                                     pose proof (not_In_preserves_eq sout (VarSet.add cond_var (VarSet.union (apply_inv_phi (BlockD.phi_function next_b0_if_true bid) s1') (apply_inv_phi (BlockD.phi_function next_b bid) s2'))) v H_sout H_not_In_v_s) as H_not_In_v_s'.
                                     unfold apply_inv_phi in H_not_In_v_s'.
                                     rewrite <- E_phi_invars in H_not_In_v_s'.
                                     rewrite <- E_phi_outvars in H_not_In_v_s'.
                                     rewrite VarSet.add_spec in H_not_In_v_s'.
                                     apply Decidable.not_or in H_not_In_v_s' as [_ H_not_In_v_s'].
                                     rewrite VarSet.union_spec in H_not_In_v_s'.
                                     apply Decidable.not_or in H_not_In_v_s' as [_ H_not_In_v_s'].
                                     rewrite VarSet.union_spec in H_not_In_v_s'.
                                     apply Decidable.not_or in H_not_In_v_s' as [H_not_In_v_s' _].
                                     rewrite VarSet.diff_spec in H_not_In_v_s'.
                                     apply Decidable.not_and in H_not_In_v_s' as [H_not_In_v_s' | H_not_In_v_s' ].
                                     ******** apply H_not_In_v_s'.
                                     ******** apply Decidable.not_not in H_not_In_v_s'.
                                     rewrite <- list_to_set_spec in H_not_In_v_s'.
                                     contradiction H_not_In_v_s'.
                                     apply varset_in_dec.
                                     ******** apply varset_in_dec.
                                   }.


                                   apply (assign_all_preserves_eq_up_to phi_outvars (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) v (SmallStepD.eval_sexpr phi_invars sf1) var_assignments_1 var_assignments_2 H_v_not_in_output H_equiv_assign_sf1_sf2 E_assign_all_1 E_assign_all_2).

                                   apply (accessed_var_instr_neq_v p fname next_bid next_b 0%nat s0 v0 s2' v E_next_b H_live_at_pc_if_false H_not_v_In_s'' H_accessed_vars H_In_v0_s0).

                       ***** rewrite (assign_all_none phi_outvars (SmallStepD.eval_sexpr phi_invars sf1) (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) E_assign_all_1).

                             remember (SmallStepD.StateD.set_status st2 (Status.Error "Error while applying phi-function")) as st2' eqn:E_st2'.

                             exists st2'.
                             exists bid.
                             exists b.
                             exists pc.
                             exists sout.
                             repeat split.
                             ****** apply H_b_exists.
                             ****** left.
                                    repeat split.
                                    ******* rewrite <- H_handle_block_finish.
                                            simpl.
                                            apply H_lt_i.
                                   ******* rewrite <- H_handle_block_finish.
                                           rewrite E_st2'.
                                           simpl.
                                           apply H_len_call_stack.
                                   ******* rewrite <- H_handle_block_finish.
                                           rewrite E_st2'.
                                           simpl.
                                           reflexivity.
                                   ******* rewrite <- H_handle_block_finish.
                                           rewrite E_st2'.
                                           simpl.
                                           apply H_dialect.
                                   ******* exists [].
                                           exists tl.
                                           exists sf1.
                                           exists sf2.
                                           repeat split.
                                           ******** rewrite <- H_handle_block_finish.
                                                    simpl.
                                                    apply H_lt_i.
                                           ******** rewrite <- H_handle_block_finish.
                                                    simpl.
                                                    apply H_call_stack_st1.
                                           ******** apply H_len_tl_st1.
                                           ******** rewrite E_st2'.
                                                    simpl.
                                                    rewrite H_call_stack_st1 in H_lt_i.
                                                    simpl in H_lt_i.
                                                    rewrite H_call_stack_st2.
                                                    simpl.
                                                    apply H_lt_i.
                                           ******** rewrite E_st2'.
                                                    simpl.
                                                    apply H_call_stack_st2.
                                           ******** apply H_len_tl_st2.
                                           ******** apply H_fname_sf1.
                                           ******** apply H_bid_sf1.
                                           ******** apply H_pc_sf1.
                                           ******** apply H_fname_sf2.
                                           ******** apply H_bid_sf2.
                                           ******** apply H_pc_sf2.
                                           ******** apply H_equiv_assign_sf1_sf2.
                                   ******* apply H_live_at_pc.
                                   ******* apply H_not_In_v_s.
                             ****** rewrite <- H_handle_block_finish.
                                    rewrite E_st2'.
                                    unfold equiv_vars_in_top_frame.
                                    simpl.
                                    rewrite H_call_stack_st1.
                                    rewrite H_call_stack_st2.
                                    repeat split.
                                    ******* rewrite H_fname_sf1. rewrite H_fname_sf2. reflexivity.
                                    ******* rewrite H_bid_sf1. rewrite H_bid_sf2. reflexivity.
                                    ******* rewrite H_pc_sf1. rewrite H_pc_sf2. reflexivity.
                                    ******* intros v0 s0 H_accessed_vars H_In_v0_s0.
                                            pose proof (accessed_var_instr_neq_v p fname bid b pc s0 v0 sout v H_b_exists H_live_at_pc H_not_In_v_s H_accessed_vars H_In_v0_s0) as H_v0_neq_v.
                                            apply (H_equiv_assign_sf1_sf2 v0 H_v0_neq_v).

              (* block not found *)
              *** remember (SmallStepD.StateD.set_status st2 (Status.Error "Target block not found in the smart contract")) as st2' eqn:H_st2'.
                  exists st2'.
                  exists bid.
                  exists b.
                  exists pc.
                  exists sout.
                  repeat split.
                  **** apply H_b_exists.
                  **** left.
                       repeat split.
                       ***** rewrite <- H_handle_block_finish.
                             simpl.
                             apply H_lt_i.
                       ***** rewrite <- H_handle_block_finish.
                             rewrite H_st2'.
                             simpl.
                             apply H_len_call_stack.
                       ***** rewrite <- H_handle_block_finish.
                             rewrite H_st2'.
                             simpl.
                             reflexivity.
                       ***** rewrite <- H_handle_block_finish.
                             rewrite H_st2'.
                             simpl.
                             apply H_dialect.
                       ***** exists [].
                             exists tl.
                             exists sf1.
                             exists sf2.
                             repeat split.
                             ****** rewrite <- H_handle_block_finish.
                                    simpl.
                                    apply H_lt_i.
                             ****** rewrite <- H_handle_block_finish.
                                    simpl.
                                    apply H_call_stack_st1.
                             ****** apply H_len_tl_st1.
                             ****** rewrite H_st2'.
                                    simpl.
                                    rewrite H_call_stack_st2.
                                    simpl.
                                    rewrite H_call_stack_st1 in H_lt_i.
                                    simpl in H_lt_i.
                                    apply H_lt_i.
                            ****** rewrite H_st2'.
                                   simpl.
                                   apply H_call_stack_st2.
                            ****** apply H_len_tl_st2.
                            ****** apply H_fname_sf1.
                            ****** apply H_bid_sf1.
                            ****** apply H_pc_sf1.
                            ****** apply H_fname_sf2.
                            ****** apply H_bid_sf2.
                            ****** apply H_pc_sf2.
                            ****** apply H_equiv_assign_sf1_sf2.
                       ***** apply H_live_at_pc.
                       ***** apply H_not_In_v_s.
                  **** rewrite <- H_handle_block_finish.
                       rewrite H_st2'.
                       unfold equiv_vars_in_top_frame.
                       simpl.
                       rewrite H_call_stack_st1.
                       rewrite H_call_stack_st2.
                       repeat split.
                       ***** rewrite H_fname_sf1. rewrite H_fname_sf2. reflexivity.
                       ***** rewrite H_bid_sf1. rewrite H_bid_sf2. reflexivity.
                       ***** rewrite H_pc_sf1. rewrite H_pc_sf2. reflexivity.
                       ***** intros v0 s0 H_accessed_vars H_In_v0_s0.
                             pose proof (accessed_var_instr_neq_v p fname bid b pc s0 v0 sout v H_b_exists H_live_at_pc H_not_In_v_s H_accessed_vars H_In_v0_s0) as H_v0_neq_v.
                             apply (H_equiv_assign_sf1_sf2 v0 H_v0_neq_v).

                 

                
         *  (* cannot be the case of pc<length b *)
             rewrite H_b_exists in H_b0_exists.
             injection H_b0_exists as H_b0_exists.
             subst b0.
             unfold SmallStepD.get_next_instruction in H_get_instr.
             rewrite H_call_stack_st1 in H_get_instr.
             unfold SmallStepD.SmartContractD.get_instruction in H_get_instr.
             rewrite H_fname_sf1 in H_get_instr.
             rewrite H_bid_sf1 in H_get_instr.
             rewrite H_pc_sf1 in H_get_instr.
             rewrite H_b_exists in H_get_instr.
             rewrite H_get_instr in H_get_instr'.
             discriminate H_get_instr'.




       (* conditional jump ends here *)

 
      (* jump block *)
      + destruct (SmallStepD.SmartContractD.get_block p fname next_bid) as [next_b|] eqn:E_next_b.
        
        * (* block found *)

          assert( H_live_at_pc' :=  H_live_at_pc).

          
          destruct H_live_at_pc' as [fname bid b0 pc s sout H_b0_exists H_live_out H_pc_at_end H_sout | fname bid b0 pc s sout instr' H_b0_exists H_live_at_S_pc H_lt_pc' H_get_instr' H_sout].

          ** rewrite H_b_exists in H_b0_exists.
             injection H_b0_exists as H_b0_exists.
             subst b0.
             
             destruct H_live_out as [ fname bid b0 rs' sout0 H_b0_exists H_is_ret H_sout0| fname bid b0 sout0 H_b0_exists H_is_termin | fname bid next_bid' b0 next_b0 s' sout0 H_b0_exists H_is_jump H_live_in_next_pc H_next_b0_exists H_sout0 | fname bid  next_bid_if_true next_bid_if_false cvar b0 next_b0_if_true next_b0_if_false s1' s2' sout0 H_b0_exists H_is_cjump ].

             ***  rewrite H_b_exists in H_b0_exists.
                  injection H_b0_exists as H_b0_exists.
                  subst b0.
                  unfold BlockD.is_return_block in H_is_ret.
                  rewrite E_b_exit_info in H_is_ret.
                  discriminate H_is_ret.
             *** rewrite H_b_exists in H_b0_exists.
                 injection H_b0_exists as H_b0_exists.
                 subst b0.
                 unfold BlockD.is_terminated_block in H_is_termin.
                 rewrite E_b_exit_info in H_is_termin.
                 discriminate H_is_termin.

             *** rewrite H_b_exists in H_b0_exists.
                 injection H_b0_exists as H_b0_exists.
                 subst b0.
                 unfold add_jump_var_if_applicable in H_sout.
                 rewrite E_b_exit_info in H_sout.
                 rewrite H_sout0 in H_sout.

                 unfold BlockD.is_jump_block in H_is_jump.
                 rewrite E_b_exit_info in H_is_jump.
                 injection H_is_jump as H_is_jump.
                 subst next_bid'.

                 rewrite E_next_b in H_next_b0_exists.
                 injection H_next_b0_exists as H_next_b0_exists.
                 subst next_b0.
                 

                 
                 unfold SmallStepD.apply_renamings in H_handle_block_finish.
                 unfold SmallStepD.apply_renamings.

                 remember (SmallStepD.get_renaming_sexpr (SmallStepD.SmartContractD.BlockD.phi_function next_b bid)) as phi_invars eqn:E_phi_invars.

                 remember (SmallStepD.get_renaming_var (SmallStepD.SmartContractD.BlockD.phi_function next_b bid)) as phi_outvars eqn:E_phi_outvars.
                 
                 assert (H_not_In_v_input: ~ In (inl v) phi_invars).
                 {
                   pose proof (not_In_preserves_eq sout (apply_inv_phi (BlockD.phi_function next_b bid) s') v H_sout H_not_In_v_s) as H_v_not_in_inv.
                   unfold apply_inv_phi in H_v_not_in_inv.
                   rewrite <- E_phi_invars in H_v_not_in_inv.
                   rewrite <- E_phi_outvars in H_v_not_in_inv.

                   rewrite VarSet.union_spec in H_v_not_in_inv.
                   apply Decidable.not_or in H_v_not_in_inv.
                   destruct H_v_not_in_inv as [_ H_v_not_in_inv].
                   rewrite <- list_to_set_spec in  H_v_not_in_inv.
                   rewrite <- extract_yul_vars_spec in H_v_not_in_inv.
                   apply H_v_not_in_inv.
                 }.

                 rewrite <- (eval_sexpr_snd phi_invars fname bid pc v sf1 sf2 H_equiv_sf1_sf2 H_not_In_v_input).

                 destruct (SmallStepD.VariableAssignmentD.assign_all (SmallStepD.StackFrameD.variable_assignments sf1) phi_outvars (SmallStepD.eval_sexpr phi_invars sf1)) as [var_assignments_1|] eqn:E_assign_all_1.

                 **** pose proof (assign_all_some phi_outvars (SmallStepD.eval_sexpr phi_invars sf1) (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) var_assignments_1 E_assign_all_1) as [var_assignments_2 E_assign_all_2].
                      rewrite E_assign_all_2.

                      rewrite <- live_at_pc_zero_eq_live_in in H_live_in_next_pc.
                      rewrite (live_at_pc'_0_equiv_live_at_pc_0 p fname next_bid next_b s' E_next_b) in H_live_in_next_pc.
                      
                      remember {|
                                  Liveness_snd.StateD.call_stack :=
                                    {|
                                      Liveness_snd.StackFrameD.function_name := fname;
                                      Liveness_snd.StackFrameD.variable_assignments := var_assignments_2;
                                      Liveness_snd.StackFrameD.curr_block_id := next_bid;
                                      Liveness_snd.StackFrameD.pc := 0
                                    |} :: tl;
                          Liveness_snd.StateD.status := Status.Running;
                          Liveness_snd.StateD.dialect_state := SmallStepD.StateD.dialect_state st2
                        |} as st2' eqn:E_st2'.
                      exists st2'.
                      exists next_bid.
                      exists next_b.
                      exists 0%nat.
                      exists s'.
                      repeat split.
                      ***** apply E_next_b.
                      ***** (* split on wether v is in the phi_outvars *)
                            pose proof (varlist_in_dec phi_outvars v) as H_v_output.
                      
                            destruct H_v_output as [H_v_in_output | H_v_not_in_output].
                            ****** right.
                                   rewrite <- (assign_all_preserves_eq_up_to_eq phi_outvars (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) v (SmallStepD.eval_sexpr phi_invars sf1) var_assignments_1 var_assignments_2 H_v_in_output H_equiv_assign_sf1_sf2 E_assign_all_1 E_assign_all_2) in E_st2'.
                            
                                   rewrite E_st2'.
                                   rewrite <- H_handle_block_finish.
                                   rewrite H_dialect.
                                   reflexivity.
                            ****** left.
                                   repeat split.
                                   ******* rewrite <- H_handle_block_finish.
                                           simpl.
                                           rewrite H_call_stack_st1 in H_lt_i.
                                           simpl in H_lt_i.
                                           apply H_lt_i.
                                   ******* rewrite <- H_handle_block_finish.
                                           rewrite E_st2'.
                                           simpl.
                                           reflexivity.
                                   ******* rewrite <- H_handle_block_finish.
                                           rewrite E_st2'.
                                           simpl.
                                           reflexivity.
                                   ******* rewrite <- H_handle_block_finish.
                                           rewrite E_st2'.
                                           simpl.
                                           apply H_dialect.
                                   ******* exists [].
                                           exists tl.
                                           exists {|
                                               Liveness_snd.StackFrameD.function_name := fname;
                                               Liveness_snd.StackFrameD.variable_assignments := var_assignments_1;
                                               Liveness_snd.StackFrameD.curr_block_id := next_bid;
                                               Liveness_snd.StackFrameD.pc := 0
                                             |}.
                                           exists {|
                                               Liveness_snd.StackFrameD.function_name := fname;
                                               Liveness_snd.StackFrameD.variable_assignments := var_assignments_2;
                                               Liveness_snd.StackFrameD.curr_block_id := next_bid;
                                               Liveness_snd.StackFrameD.pc := 0
                                             |}.
                                           repeat split.
                                           ******** rewrite <- H_handle_block_finish.
                                                    simpl.
                                                    rewrite H_call_stack_st1 in H_lt_i.
                                                    simpl in H_lt_i.
                                                    apply H_lt_i.
                                           ******** rewrite <- H_handle_block_finish.
                                                    simpl.     
                                                    reflexivity.
                                           ******** apply H_len_tl_st1.
                                           ******** rewrite E_st2'.
                                                    simpl.
                                                    rewrite H_call_stack_st1 in H_lt_i.
                                                    simpl in H_lt_i.
                                                    apply H_lt_i.
                                           ******** rewrite E_st2'.
                                                    simpl.
                                                    reflexivity.
                                           ******** apply H_len_tl_st2.
                                           ******** simpl.
                                                    apply (assign_all_preserves_eq_up_to phi_outvars (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) v (SmallStepD.eval_sexpr phi_invars sf1) var_assignments_1 var_assignments_2 H_v_not_in_output H_equiv_assign_sf1_sf2 E_assign_all_1 E_assign_all_2).
                                   ******* apply H_live_in_next_pc.
                                   ******* pose proof (not_In_preserves_eq sout (apply_inv_phi (BlockD.phi_function next_b bid) s') v H_sout H_not_In_v_s) as H_not_In_v_s'.
                                           unfold apply_inv_phi in H_not_In_v_s'.
                                           rewrite <- E_phi_invars in H_not_In_v_s'.
                                           rewrite <- E_phi_outvars in H_not_In_v_s'.
                                           rewrite VarSet.union_spec in H_not_In_v_s'.
                                           apply Decidable.not_or in H_not_In_v_s' as [H_not_In_v_s' _].
                                           rewrite VarSet.diff_spec in H_not_In_v_s'.
                                           apply Decidable.not_and in H_not_In_v_s' as [H_not_In_v_s' | H_not_In_v_s' ].
                                           ******** apply H_not_In_v_s'.
                                           ******** apply Decidable.not_not in H_not_In_v_s'.
                                                    rewrite <- list_to_set_spec in H_not_In_v_s'.
                                                    contradiction H_not_In_v_s'.
                                                    apply varset_in_dec.
                                           ******** apply varset_in_dec.

                      ***** (* split on wether v is in the phi_outvars *)
                            pose proof (varlist_in_dec phi_outvars v) as H_v_output.
                      
                            destruct H_v_output as [H_v_in_output | H_v_not_in_output].
                      
                            ****** rewrite <- (assign_all_preserves_eq_up_to_eq phi_outvars (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) v (SmallStepD.eval_sexpr phi_invars sf1) var_assignments_1 var_assignments_2 H_v_in_output H_equiv_assign_sf1_sf2 E_assign_all_1 E_assign_all_2) in E_st2'.
                            
                                   rewrite E_st2'.
                                   rewrite <- H_handle_block_finish.
                                   rewrite H_dialect.
                                   unfold equiv_vars_in_top_frame.
                                   simpl.
                                   repeat split; try reflexivity.
                            
                            ****** rewrite <- H_handle_block_finish.
                                   rewrite E_st2'.
                                   unfold equiv_vars_in_top_frame.
                                   simpl.
                                   repeat split; try reflexivity.
                                   intros v0 s0 H_accessed_vars H_In_v0_s0.


                                   assert(H_not_v_In_s'': ~ VarSet.In v s').
                                   {
                                     pose proof (not_In_preserves_eq sout (apply_inv_phi (BlockD.phi_function next_b bid) s') v H_sout H_not_In_v_s) as H_not_In_v_s'.
                                     unfold apply_inv_phi in H_not_In_v_s'.
                                     rewrite <- E_phi_invars in H_not_In_v_s'.
                                     rewrite <- E_phi_outvars in H_not_In_v_s'.
                                     rewrite VarSet.union_spec in H_not_In_v_s'.
                                     apply Decidable.not_or in H_not_In_v_s' as [H_not_In_v_s' _].
                                     rewrite VarSet.diff_spec in H_not_In_v_s'.
                                     apply Decidable.not_and in H_not_In_v_s' as [H_not_In_v_s' | H_not_In_v_s' ].
                                     ******** apply H_not_In_v_s'.
                                     ******** apply Decidable.not_not in H_not_In_v_s'.
                                     rewrite <- list_to_set_spec in H_not_In_v_s'.
                                     contradiction H_not_In_v_s'.
                                     apply varset_in_dec.
                                     ******** apply varset_in_dec.
                                   }


                                   apply (assign_all_preserves_eq_up_to phi_outvars (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) v (SmallStepD.eval_sexpr phi_invars sf1) var_assignments_1 var_assignments_2 H_v_not_in_output H_equiv_assign_sf1_sf2 E_assign_all_1 E_assign_all_2).

                                   apply (accessed_var_instr_neq_v p fname next_bid next_b 0%nat s0 v0 s' v E_next_b H_live_in_next_pc H_not_v_In_s'' H_accessed_vars H_In_v0_s0).



                      
                 **** rewrite (assign_all_none phi_outvars (SmallStepD.eval_sexpr phi_invars sf1) (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) E_assign_all_1).

                      remember (SmallStepD.StateD.set_status st2 (Status.Error "Error while applying phi-function")) as st2' eqn:E_st2'.

                      exists st2'.
                      exists bid.
                      exists b.
                      exists pc.
                      exists sout.
                      repeat split.
                      ***** apply H_b_exists.
                      ***** left.
                            repeat split.
                            ****** rewrite <- H_handle_block_finish.
                                   simpl.
                                   apply H_lt_i.
                            ****** rewrite <- H_handle_block_finish.
                                   rewrite E_st2'.
                                   simpl.
                                   apply H_len_call_stack.
                            ****** rewrite <- H_handle_block_finish.
                                   rewrite E_st2'.
                                   simpl.
                                   reflexivity.
                            ****** rewrite <- H_handle_block_finish.
                                   rewrite E_st2'.
                                   simpl.
                                   apply H_dialect.
                            ****** exists [].
                                   exists tl.
                                   exists sf1.
                                   exists sf2.
                                   repeat split.
                                   ******* rewrite <- H_handle_block_finish.
                                           simpl.
                                           apply H_lt_i.
                                   ******* rewrite <- H_handle_block_finish.
                                           simpl.
                                           apply H_call_stack_st1.
                                   ******* apply H_len_tl_st1.
                                   ******* rewrite E_st2'.
                                           simpl.
                                           rewrite H_call_stack_st1 in H_lt_i.
                                           simpl in H_lt_i.
                                           rewrite H_call_stack_st2.
                                           simpl.
                                           apply H_lt_i.
                                   ******* rewrite E_st2'.
                                           simpl.
                                           apply H_call_stack_st2.
                                   ******* apply H_len_tl_st2.
                                   ******* apply H_fname_sf1.
                                   ******* apply H_bid_sf1.
                                   ******* apply H_pc_sf1.
                                   ******* apply H_fname_sf2.
                                   ******* apply H_bid_sf2.
                                   ******* apply H_pc_sf2.
                                   ******* apply H_equiv_assign_sf1_sf2.
                            ****** apply H_live_at_pc.
                            ****** apply H_not_In_v_s.
                      ***** rewrite <- H_handle_block_finish.
                            rewrite E_st2'.
                            unfold equiv_vars_in_top_frame.
                            simpl.
                            rewrite H_call_stack_st1.
                            rewrite H_call_stack_st2.
                            repeat split.
                            ****** rewrite H_fname_sf1. rewrite H_fname_sf2. reflexivity.
                            ****** rewrite H_bid_sf1. rewrite H_bid_sf2. reflexivity.
                            ****** rewrite H_pc_sf1. rewrite H_pc_sf2. reflexivity.
                            ****** intros v0 s0 H_accessed_vars H_In_v0_s0.
                                   pose proof (accessed_var_instr_neq_v p fname bid b pc s0 v0 sout v H_b_exists H_live_at_pc H_not_In_v_s H_accessed_vars H_In_v0_s0) as H_v0_neq_v.
                                   apply (H_equiv_assign_sf1_sf2 v0 H_v0_neq_v).

             *** rewrite H_b_exists in H_b0_exists.
                 injection H_b0_exists as H_b0_exists.
                 subst b0.
                 unfold BlockD.is_cond_jump_block in H_is_cjump.
                 rewrite E_b_exit_info in H_is_cjump.
                 discriminate H_is_cjump.

          ** (* cannot be the case of pc<length b *)
             rewrite H_b_exists in H_b0_exists.
             injection H_b0_exists as H_b0_exists.
             subst b0.
             unfold SmallStepD.get_next_instruction in H_get_instr.
             rewrite H_call_stack_st1 in H_get_instr.
             unfold SmallStepD.SmartContractD.get_instruction in H_get_instr.
             rewrite H_fname_sf1 in H_get_instr.
             rewrite H_bid_sf1 in H_get_instr.
             rewrite H_pc_sf1 in H_get_instr.
             rewrite H_b_exists in H_get_instr.
             rewrite H_get_instr in H_get_instr'.
             discriminate H_get_instr'.

                      
        * (* block not found *)
          remember (SmallStepD.StateD.set_status st2 (Status.Error "Target block not found in the smart contract")) as st2' eqn:H_st2'.
          exists st2'.
          exists bid.
          exists b.
          exists pc.
          exists s.
          repeat split.
          ** apply H_b_exists.
          ** left.
             repeat split.
             *** rewrite <- H_handle_block_finish.
                 simpl.
                 apply H_lt_i.
             *** rewrite <- H_handle_block_finish.
                 rewrite H_st2'.
                 simpl.
                 apply H_len_call_stack.
             *** rewrite <- H_handle_block_finish.
                 rewrite H_st2'.
                 simpl.
                 reflexivity.
             *** rewrite <- H_handle_block_finish.
                 rewrite H_st2'.
                 simpl.
                 apply H_dialect.
             *** exists [].
                 exists tl.
                 exists sf1.
                 exists sf2.
                 repeat split.
                 **** rewrite <- H_handle_block_finish.
                      simpl.
                      apply H_lt_i.
                 **** rewrite <- H_handle_block_finish.
                      simpl.
                      apply H_call_stack_st1.
                 **** apply H_len_tl_st1.
                 **** rewrite H_st2'.
                      simpl.
                      rewrite H_call_stack_st2.
                      simpl.
                      rewrite H_call_stack_st1 in H_lt_i.
                      simpl in H_lt_i.
                      apply H_lt_i.
                 **** rewrite H_st2'.
                      simpl.
                      apply H_call_stack_st2.
                 **** apply H_len_tl_st2.
                 **** apply H_fname_sf1.
                 **** apply H_bid_sf1.
                 **** apply H_pc_sf1.
                 **** apply H_fname_sf2.
                 **** apply H_bid_sf2.
                 **** apply H_pc_sf2.
                 **** apply H_equiv_assign_sf1_sf2.
             *** apply H_live_at_pc.
             *** apply H_not_In_v_s.
          ** rewrite <- H_handle_block_finish.
             rewrite H_st2'.
             unfold equiv_vars_in_top_frame.
             simpl.
             rewrite H_call_stack_st1.
             rewrite H_call_stack_st2.
             repeat split.
             *** rewrite H_fname_sf1. rewrite H_fname_sf2. reflexivity.
             *** rewrite H_bid_sf1. rewrite H_bid_sf2. reflexivity.
             *** rewrite H_pc_sf1. rewrite H_pc_sf2. reflexivity.
             *** intros v0 s0 H_accessed_vars H_In_v0_s0.
                 pose proof (accessed_var_instr_neq_v p fname bid b pc s0 v0 s v H_b_exists H_live_at_pc H_not_In_v_s H_accessed_vars H_In_v0_s0) as H_v0_neq_v.
                 apply (H_equiv_assign_sf1_sf2 v0 H_v0_neq_v).



          
      (* return block *)
      + destruct tl as [|ret_sf tl'] eqn:E_tl. (* destruct on wether sf1/sf2 are the only frames *)
        * remember (SmallStepD.StateD.set_status st2 (Status.Error "Missing return stack frame")) as st2' eqn:H_st2'.
          exists st2'.
          exists bid.
          exists b.
          exists pc.
          exists s.
          repeat split.
          ** apply H_b_exists.
          ** left.
             repeat split.
             *** rewrite <- H_handle_block_finish.
                 simpl.
                 apply H_lt_i.
             *** rewrite <- H_handle_block_finish.
                 rewrite H_st2'.
                 simpl.
                 apply H_len_call_stack.
             *** rewrite <- H_handle_block_finish.
                 rewrite H_st2'.
                 simpl.
                 reflexivity.
             *** rewrite <- H_handle_block_finish.
                 rewrite H_st2'.
                 simpl.
                 apply H_dialect.
             *** exists [].
                 exists [].
                 exists sf1.
                 exists sf2.
                 repeat split.
                 **** rewrite <- H_handle_block_finish.
                      simpl.
                      apply H_lt_i.
                 **** rewrite <- H_handle_block_finish.
                      simpl.
                      apply H_call_stack_st1.
                 **** apply H_len_tl_st1.
                 **** rewrite H_st2'.
                      simpl.
                      rewrite H_call_stack_st2.
                      simpl.
                      rewrite H_call_stack_st1 in H_lt_i.
                      simpl in H_lt_i.
                      apply H_lt_i.
                 **** rewrite H_st2'.
                      simpl.
                      apply H_call_stack_st2.
                 **** apply H_len_tl_st2.
                 **** apply H_fname_sf1.
                 **** apply H_bid_sf1.
                 **** apply H_pc_sf1.
                 **** apply H_fname_sf2.
                 **** apply H_bid_sf2.
                 **** apply H_pc_sf2.
                 **** apply H_equiv_assign_sf1_sf2.
             *** apply H_live_at_pc.
             *** apply H_not_In_v_s.
          ** rewrite <- H_handle_block_finish.
             rewrite H_st2'.
             unfold equiv_vars_in_top_frame.
             simpl.
             rewrite H_call_stack_st1.
             rewrite H_call_stack_st2.
             repeat split.
             *** rewrite H_fname_sf1. rewrite H_fname_sf2. reflexivity.
             *** rewrite H_bid_sf1. rewrite H_bid_sf2. reflexivity.
             *** rewrite H_pc_sf1. rewrite H_pc_sf2. reflexivity.
             *** intros v0 s0 H_accessed_vars H_In_v0_s0.
                 pose proof (accessed_var_instr_neq_v p fname bid b pc s0 v0 s v H_b_exists H_live_at_pc H_not_In_v_s H_accessed_vars H_In_v0_s0) as H_v0_neq_v.
                 apply (H_equiv_assign_sf1_sf2 v0 H_v0_neq_v).

        * destruct (SmallStepD.SmartContractD.get_block p (SmallStepD.StackFrameD.function_name ret_sf) (SmallStepD.StackFrameD.curr_block_id ret_sf)) as [ret_b | ] eqn:E_ret_b.

          ** (* return block found *)
             destruct (nth_error (SmallStepD.BlockD.instructions ret_b) (SmallStepD.StackFrameD.pc ret_sf)) as [instr|] eqn:E_ret_instr.

             *** (* return instruction found *)

               assert( H_live_at_pc' :=  H_live_at_pc).
               
               (* we want to show that v is not in the return values *)
               destruct H_live_at_pc' as [fname bid b0 pc s sout H_b0_exists H_live_out H_pc_at_end H_sout | fname bid b0 pc s sout instr' H_b0_exists H_live_at_S_pc H_lt_pc' H_get_instr' H_sout].

                  **** rewrite H_b_exists in H_b0_exists.
                       injection H_b0_exists as H_b0_exists.
                       subst b0.
                       destruct H_live_out as [ fname bid b0 rs' sout0 H_b0_exists H_is_ret H_sout0| fname bid b0 sout0 H_b0_exists H_is_termin | fname bid next_bid b0 next_b0 s' sout0 H_b0_exists H_is_jump | fname bid  next_bid_if_true next_bid_if_false cvar b0 next_b0_if_true next_b0_if_false s1' s2' sout0 H_b0_exists H_is_cjump ].
                       ***** rewrite H_b_exists in H_b0_exists.
                             injection H_b0_exists as H_b0_exists.
                             subst b0.
                             unfold BlockD.is_return_block in H_is_ret.
                             rewrite E_b_exit_info in H_is_ret.
                             injection H_is_ret as H_is_ret.
                             subst rs'.
                             unfold add_jump_var_if_applicable in H_sout.
                             rewrite E_b_exit_info in H_sout.
                             rewrite H_sout0 in H_sout.
                             pose proof (not_In_preserves_eq sout (list_to_set (extract_yul_vars rs)) v H_sout H_not_In_v_s) as H_not_in_v_set_rs.
                             rewrite <- list_to_set_spec in H_not_in_v_set_rs.
                             rewrite <- extract_yul_vars_spec in H_not_in_v_set_rs.
                              
                             rewrite <- (eval_sexpr_snd rs fname bid pc v sf1 sf2 H_equiv_sf1_sf2 H_not_in_v_set_rs).

                             destruct (SmallStepD.VariableAssignmentD.assign_all (SmallStepD.StackFrameD.variable_assignments ret_sf) (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) (SmallStepD.eval_sexpr rs sf1)) as [prev_sf_var_assignment'|] eqn:E_assign_all.
                             ****** remember {|
                                                Liveness_snd.StateD.call_stack :=
                                                 {|
                                                   Liveness_snd.StackFrameD.function_name := SmallStepD.StackFrameD.function_name ret_sf;
                                                   Liveness_snd.StackFrameD.variable_assignments := prev_sf_var_assignment';
                                                   Liveness_snd.StackFrameD.curr_block_id := SmallStepD.StackFrameD.curr_block_id ret_sf;
                                                   Liveness_snd.StackFrameD.pc := SmallStepD.StackFrameD.pc ret_sf + 1
                                                 |} :: tl';
                                               Liveness_snd.StateD.status := Status.Running;
                                        Liveness_snd.StateD.dialect_state := SmallStepD.StateD.dialect_state st2
                                      |} as st2' eqn:H_st2'.

                                      exists st2'. (* we are not going to use it *)
                                      exists bid. (* we are not going to use it *)
                                      exists b. (* we are not going to use it *)
                                      exists pc. (* we are not going to use it *)
                                      exists VarSet.empty. (* we are not going to use it *)
                                      repeat split.
                                      ******* apply H_b_exists.
                                      ******* right.
                                              rewrite H_st2'.
                                              rewrite <- H_handle_block_finish.
                                              simpl.
                                              rewrite H_dialect.
                                              reflexivity.
                                      ******* rewrite H_st2'.
                                              rewrite <- H_handle_block_finish.
                                              simpl.
                                              unfold equiv_vars_in_top_frame.
                                              simpl.
                                              repeat split.
                                      
                             ****** remember (SmallStepD.StateD.set_status st2 (Status.Error "Failed to assign return values")) as st2' eqn:H_st2'.
                                    exists st2'.
                                    exists bid.
                                    exists b.
                                    exists pc.
                                    exists sout.
                                    repeat split.
                                    ******* apply H_b_exists.
                                    ******* left.
                                            repeat split.
                                            ******** rewrite <- H_handle_block_finish.
                                                     simpl.
                                                     apply H_lt_i.
                                            ******** rewrite <- H_handle_block_finish.
                                                     rewrite H_st2'.
                                                     simpl.
                                                     apply H_len_call_stack.
                                            ******** rewrite <- H_handle_block_finish.
                                                     rewrite H_st2'.
                                                     simpl.
                                                     reflexivity.
                                            ******** rewrite <- H_handle_block_finish.
                                                     rewrite H_st2'.
                                                     simpl.
                                                     apply H_dialect.
                                            ******** exists [].
                                                     exists (ret_sf :: tl').
                                                     exists sf1.
                                                     exists sf2.
                                                     repeat split.
                                                     ********* rewrite <- H_handle_block_finish.
                                                               simpl.
                                                               apply H_lt_i.
                                                     ********* rewrite <- H_handle_block_finish.
                                                                simpl.
                                                                apply H_call_stack_st1.
                                                     ********* apply H_len_tl_st1.
                                                     ********* rewrite H_st2'.
                                                               simpl.
                                                               rewrite H_call_stack_st2.
                                                               simpl.
                                                               rewrite H_call_stack_st1 in H_lt_i.
                                                               simpl in H_lt_i.
                                                               apply H_lt_i.
                                                     ********* rewrite H_st2'.
                                                               simpl.
                                                               apply H_call_stack_st2.
                                                     ********* apply H_len_tl_st2.
                                                     ********* apply H_fname_sf1.
                                                     ********* apply H_bid_sf1.
                                                     ********* apply H_pc_sf1.
                                                     ********* apply H_fname_sf2.
                                                     ********* apply H_bid_sf2.
                                                     ********* apply H_pc_sf2.
                                                     ********* apply H_equiv_assign_sf1_sf2.
                                            ******** apply H_live_at_pc.
                                            ******** apply H_not_In_v_s.
                                    ******* rewrite <- H_handle_block_finish.
                                            rewrite H_st2'.
                                            unfold equiv_vars_in_top_frame.
                                            simpl.
                                            rewrite H_call_stack_st1.
                                            rewrite H_call_stack_st2.
                                            repeat split.
                                            ******** rewrite H_fname_sf1. rewrite H_fname_sf2. reflexivity.
                                            ******** rewrite H_bid_sf1. rewrite H_bid_sf2. reflexivity.
                                            ******** rewrite H_pc_sf1. rewrite H_pc_sf2. reflexivity.
                                            ******** intros v0 s0 H_accessed_vars H_In_v0_s0.
                                                     pose proof (accessed_var_instr_neq_v p fname bid b pc s0 v0 sout v H_b_exists H_live_at_pc H_not_In_v_s H_accessed_vars H_In_v0_s0) as H_v0_neq_v.
                                                     apply (H_equiv_assign_sf1_sf2 v0 H_v0_neq_v).

                            
                       ***** rewrite H_b_exists in H_b0_exists.
                             injection H_b0_exists as H_b0_exists.
                             subst b0.
                             unfold BlockD.is_terminated_block in H_is_termin.
                             rewrite E_b_exit_info in H_is_termin.
                             discriminate H_is_termin.
                       ***** rewrite H_b_exists in H_b0_exists.
                             injection H_b0_exists as H_b0_exists.
                             subst b0.
                             unfold BlockD.is_jump_block in H_is_jump.
                             rewrite E_b_exit_info in H_is_jump.
                             discriminate H_is_jump.
                       ***** rewrite H_b_exists in H_b0_exists.
                             injection H_b0_exists as H_b0_exists.
                             subst b0.
                             unfold BlockD.is_cond_jump_block in H_is_cjump.
                             rewrite E_b_exit_info in H_is_cjump.
                             discriminate H_is_cjump.

                       
                  **** (* cannot be the case of pc<length b *)
                       rewrite H_b_exists in H_b0_exists.
                       injection H_b0_exists as H_b0_exists.
                       subst b0.
                       unfold SmallStepD.get_next_instruction in H_get_instr.
                       rewrite H_call_stack_st1 in H_get_instr.
                       unfold SmallStepD.SmartContractD.get_instruction in H_get_instr.
                       rewrite H_fname_sf1 in H_get_instr.
                       rewrite H_bid_sf1 in H_get_instr.
                       rewrite H_pc_sf1 in H_get_instr.
                       rewrite H_b_exists in H_get_instr.
                       rewrite H_get_instr in H_get_instr'.
                       discriminate H_get_instr'.
               
             *** (* return instruction not found *)
                 remember (SmallStepD.StateD.set_status st2 (Status.Error "Failed to find call instruction")) as st2' eqn:H_st2'.
                 exists st2'.
                 exists bid.
                 exists b.
                 exists pc.
                 exists s.
                 repeat split.
                 **** apply H_b_exists.
                 **** left.
                      repeat split.
                      ***** rewrite <- H_handle_block_finish.
                            simpl.
                            apply H_lt_i.
                      ***** rewrite <- H_handle_block_finish.
                            rewrite H_st2'.
                            simpl.
                            apply H_len_call_stack.
                      ***** rewrite <- H_handle_block_finish.
                            rewrite H_st2'.
                            simpl.
                            reflexivity.
                      ***** rewrite <- H_handle_block_finish.
                            rewrite H_st2'.
                            simpl.
                            apply H_dialect.
                      ***** exists [].
                            exists (ret_sf :: tl').
                            exists sf1.
                            exists sf2.
                            repeat split.
                            ****** rewrite <- H_handle_block_finish.
                                   simpl.
                                   apply H_lt_i.
                            ****** rewrite <- H_handle_block_finish.
                                   simpl.
                                   apply H_call_stack_st1.
                            ****** apply H_len_tl_st1.
                            ****** rewrite H_st2'.
                                   simpl.
                                   rewrite H_call_stack_st2.
                                   simpl.
                                   rewrite H_call_stack_st1 in H_lt_i.
                                   simpl in H_lt_i.
                                   apply H_lt_i.
                            ****** rewrite H_st2'.
                                   simpl.
                                   apply H_call_stack_st2.
                            ****** apply H_len_tl_st2.
                            ****** apply H_fname_sf1.
                            ****** apply H_bid_sf1.
                            ****** apply H_pc_sf1.
                            ****** apply H_fname_sf2.
                            ****** apply H_bid_sf2.
                            ****** apply H_pc_sf2.
                            ****** apply H_equiv_assign_sf1_sf2.
                      ***** apply H_live_at_pc.
                      ***** apply H_not_In_v_s.
                 **** rewrite <- H_handle_block_finish.
                      rewrite H_st2'.
                      unfold equiv_vars_in_top_frame.
                      simpl.
                      rewrite H_call_stack_st1.
                      rewrite H_call_stack_st2.
                      repeat split.
                      ***** rewrite H_fname_sf1. rewrite H_fname_sf2. reflexivity.
                      ***** rewrite H_bid_sf1. rewrite H_bid_sf2. reflexivity.
                      ***** rewrite H_pc_sf1. rewrite H_pc_sf2. reflexivity.
                      ***** intros v0 s0 H_accessed_vars H_In_v0_s0.
                            pose proof (accessed_var_instr_neq_v p fname bid b pc s0 v0 s v H_b_exists H_live_at_pc H_not_In_v_s H_accessed_vars H_In_v0_s0) as H_v0_neq_v.
                            apply (H_equiv_assign_sf1_sf2 v0 H_v0_neq_v).


               
          ** (* return block not found *)
             remember (SmallStepD.StateD.set_status st2 (Status.Error "Failed to calling block")) as st2' eqn:H_st2'.
             exists st2'.
             exists bid.
             exists b.
             exists pc.
             exists s.
             repeat split.
             *** apply H_b_exists.
             *** left.
                 repeat split.
                 **** rewrite <- H_handle_block_finish.
                      simpl.
                      apply H_lt_i.
                 **** rewrite <- H_handle_block_finish.
                      rewrite H_st2'.
                      simpl.
                      apply H_len_call_stack.
                 **** rewrite <- H_handle_block_finish.
                      rewrite H_st2'.
                      simpl.
                      reflexivity.
                 **** rewrite <- H_handle_block_finish.
                      rewrite H_st2'.
                      simpl.
                      apply H_dialect.
                 **** exists [].
                      exists (ret_sf :: tl').
                      exists sf1.
                      exists sf2.
                      repeat split.
                      ***** rewrite <- H_handle_block_finish.
                            simpl.
                            apply H_lt_i.
                      ***** rewrite <- H_handle_block_finish.
                            simpl.
                            apply H_call_stack_st1.
                      ***** apply H_len_tl_st1.
                      ***** rewrite H_st2'.
                            simpl.
                            rewrite H_call_stack_st2.
                            simpl.
                            rewrite H_call_stack_st1 in H_lt_i.
                            simpl in H_lt_i.
                            apply H_lt_i.
                      ***** rewrite H_st2'.
                            simpl.
                            apply H_call_stack_st2.
                      ***** apply H_len_tl_st2.
                      ***** apply H_fname_sf1.
                      ***** apply H_bid_sf1.
                      ***** apply H_pc_sf1.
                      ***** apply H_fname_sf2.
                      ***** apply H_bid_sf2.
                      ***** apply H_pc_sf2.
                      ***** apply H_equiv_assign_sf1_sf2.
                 **** apply H_live_at_pc.
                 **** apply H_not_In_v_s.
             *** rewrite <- H_handle_block_finish.
                 rewrite H_st2'.
                 unfold equiv_vars_in_top_frame.
                 simpl.
                 rewrite H_call_stack_st1.
                 rewrite H_call_stack_st2.
                 repeat split.
                 **** rewrite H_fname_sf1. rewrite H_fname_sf2. reflexivity.
                 **** rewrite H_bid_sf1. rewrite H_bid_sf2. reflexivity.
                 **** rewrite H_pc_sf1. rewrite H_pc_sf2. reflexivity.
                 **** intros v0 s0 H_accessed_vars H_In_v0_s0.
                      pose proof (accessed_var_instr_neq_v p fname bid b pc s0 v0 s v H_b_exists H_live_at_pc H_not_In_v_s H_accessed_vars H_In_v0_s0) as H_v0_neq_v.
                      apply (H_equiv_assign_sf1_sf2 v0 H_v0_neq_v).


              
      (* terminated block *)
      + remember (SmallStepD.StateD.set_status st2 Status.Terminated) as st2' eqn:H_st2'.
        exists st2'.
        exists bid.
        exists b.
        exists pc.
        exists s.
        repeat split.
        * apply H_b_exists.
        * left.
          repeat split.
          ** rewrite <- H_handle_block_finish.
             simpl.
             apply H_lt_i.
          ** rewrite <- H_handle_block_finish.
             rewrite H_st2'.
             simpl.
             apply H_len_call_stack.
          ** rewrite <- H_handle_block_finish.
             rewrite H_st2'.
             simpl.
             reflexivity.
          ** rewrite <- H_handle_block_finish.
             rewrite H_st2'.
             simpl.
             apply H_dialect.
          ** exists [].
             exists tl.
             exists sf1.
             exists sf2.
             repeat split.
             *** rewrite <- H_handle_block_finish.
                 simpl.
                 apply H_lt_i.
             *** rewrite <- H_handle_block_finish.
                 simpl.
                 apply H_call_stack_st1.
             *** apply H_len_tl_st1.
             *** rewrite H_st2'.
                 simpl.
                 rewrite H_call_stack_st2.
                 simpl.
                 rewrite H_call_stack_st1 in H_lt_i.
                 simpl in H_lt_i.
                 apply H_lt_i.
             *** rewrite H_st2'.
                 simpl.
                 apply H_call_stack_st2.
             *** apply H_len_tl_st2.
             *** apply H_fname_sf1.
             *** apply H_bid_sf1.
             *** apply H_pc_sf1.
             *** apply H_fname_sf2.
             *** apply H_bid_sf2.
             *** apply H_pc_sf2.
             *** apply H_equiv_assign_sf1_sf2.
          ** apply H_live_at_pc.
          ** apply H_not_In_v_s.
        * rewrite <- H_handle_block_finish.
          rewrite H_st2'.
          unfold equiv_vars_in_top_frame.
          simpl.
          rewrite H_call_stack_st1.
          rewrite H_call_stack_st2.
          repeat split.
          ** rewrite H_fname_sf1. rewrite H_fname_sf2. reflexivity.
          ** rewrite H_bid_sf1. rewrite H_bid_sf2. reflexivity.
          ** rewrite H_pc_sf1. rewrite H_pc_sf2. reflexivity.
          ** intros v0 s0 H_accessed_vars H_In_v0_s0.
             pose proof (accessed_var_instr_neq_v p fname bid b pc s0 v0 s v H_b_exists H_live_at_pc H_not_In_v_s H_accessed_vars H_In_v0_s0) as H_v0_neq_v.
             apply (H_equiv_assign_sf1_sf2 v0 H_v0_neq_v).

    (* the case where the top stack frames are identical, and the one with v is deeper *)
    - simpl in H_call_stack_st1.
      simpl in H_call_stack_st2.

      unfold SmallStepD.handle_block_finish in H_handle_block_finish.
      rewrite H_call_stack_st1 in H_handle_block_finish.

      unfold SmallStepD.handle_block_finish.
      rewrite H_call_stack_st2.

      destruct (SmallStepD.SmartContractD.get_block p (SmallStepD.StackFrameD.function_name top_sf) (SmallStepD.StackFrameD.curr_block_id top_sf)) as [curr_block|] eqn:E_curr_block.

      * destruct (BlockD.exit_info curr_block) as [cond_var target_if_true target_if_false|next_bid|rs|] eqn:E_b_exit_info.

        (* conditional jump *)
        ** remember (if D.is_true_value (SmallStepD.VariableAssignmentD.get (SmallStepD.StackFrameD.variable_assignments top_sf) cond_var) then target_if_true else target_if_false) as next_bid eqn:E_cond_chk.

           destruct (SmallStepD.SmartContractD.get_block p (SmallStepD.StackFrameD.function_name top_sf) next_bid) as [next_b|] eqn:E_next_b.

           (* block found *)
           *** destruct (SmallStepD.apply_renamings (SmallStepD.SmartContractD.BlockD.phi_function next_b (SmallStepD.StackFrameD.curr_block_id top_sf)) top_sf) as [var_assignments'|] eqn:E_renaming.

               **** remember {|
                                Liveness_snd.StateD.call_stack :=
                                  {|
                                    Liveness_snd.StackFrameD.function_name :=
                                      SmallStepD.StackFrameD.function_name top_sf;
                                    Liveness_snd.StackFrameD.variable_assignments := var_assignments';
                                    Liveness_snd.StackFrameD.curr_block_id := next_bid;
                                    Liveness_snd.StackFrameD.pc := 0
                                  |} :: hl' ++ sf2 :: tl;
                        Liveness_snd.StateD.status := Status.Running;
                        Liveness_snd.StateD.dialect_state := SmallStepD.StateD.dialect_state st2
                      |} as st2' eqn:H_st2'.

                    exists st2'.
                    exists bid.
                    exists b.
                    exists pc.
                    exists s.
                    repeat split; try reflexivity.
                    ***** apply H_b_exists.
                    ***** left.
                          repeat split; try reflexivity.
                          ****** rewrite <- H_handle_block_finish.
                                 simpl.
                                 rewrite length_app.
                                 rewrite Nat.add_comm.
                                 simpl.
                                 rewrite H_call_stack_st1 in H_lt_i.
                                 simpl in H_lt_i.
                                 rewrite length_app in H_lt_i.
                                 rewrite Nat.add_comm in H_lt_i.
                                 simpl in H_lt_i.
                                 apply H_lt_i.
                          ****** rewrite <- H_handle_block_finish.
                                 rewrite H_st2'.
                                 simpl.
                                 rewrite length_app.
                                 rewrite length_app.
                                 rewrite Nat.add_comm.
                                 rewrite Nat.add_comm.
                                 simpl.
                                 reflexivity.
                          ****** rewrite <- H_handle_block_finish.
                                 rewrite H_st2'.
                                 simpl.       
                                 reflexivity.
                          ****** rewrite <- H_handle_block_finish.
                                 rewrite H_st2'.
                                 simpl.       
                                 apply H_dialect.
                          ****** exists ({|
                                            Liveness_snd.StackFrameD.function_name :=
                                              SmallStepD.StackFrameD.function_name top_sf;
                                            Liveness_snd.StackFrameD.variable_assignments := var_assignments';
                                            Liveness_snd.StackFrameD.curr_block_id := next_bid;
                                            Liveness_snd.StackFrameD.pc := 0
                                          |} :: hl').
                                 exists tl.
                                 exists sf1.
                                 exists sf2.
                                 repeat split.
                                 ******* rewrite <- H_handle_block_finish.
                                         simpl.
                                         rewrite length_app.
                                         rewrite Nat.add_comm.
                                         simpl.
                                         rewrite H_call_stack_st1 in H_lt_i.
                                         simpl in H_lt_i.
                                         rewrite length_app in H_lt_i.
                                         rewrite Nat.add_comm in H_lt_i.
                                         simpl in H_lt_i.
                                         apply H_lt_i.
                                 ******* rewrite <- H_handle_block_finish.
                                         simpl.
                                         reflexivity.
                                 ******* apply H_len_tl_st1.
                                 ******* rewrite H_st2'.
                                         simpl.
                                         rewrite length_app.
                                         rewrite Nat.add_comm.
                                         simpl.
                                         rewrite H_call_stack_st1 in H_lt_i.
                                         simpl in H_lt_i.
                                         rewrite length_app in H_lt_i.
                                         rewrite Nat.add_comm in H_lt_i.
                                         simpl in H_lt_i.
                                         apply H_lt_i.
                                 ******* rewrite H_st2'.
                                         simpl.
                                         reflexivity.
                                 ******* apply H_len_tl_st2.
                                 ******* apply H_fname_sf1.
                                 ******* apply H_bid_sf1.
                                 ******* apply H_pc_sf1.
                                 ******* apply H_fname_sf2.
                                 ******* apply H_bid_sf2.
                                 ******* apply H_pc_sf2.
                                 ******* apply H_equiv_assign_sf1_sf2.
                          ****** apply H_live_at_pc.
                          ****** apply H_not_In_v_s.
                    ***** rewrite <- H_handle_block_finish.
                          rewrite H_st2'.
                          unfold equiv_vars_in_top_frame.
                          simpl.
                          repeat split; try reflexivity.      

       
               **** remember (SmallStepD.StateD.set_status st2 (Status.Error  "Error while applying phi-function")) as st2' eqn:H_st2'.
        
                    exists st2'.
                    exists bid.
                    exists b.
                    exists pc.
                    exists s.
                    repeat split.
                    ***** apply H_b_exists.
                    ***** left.
                          repeat split.
                          ****** rewrite <- H_handle_block_finish.
                                 simpl.
                                 apply H_lt_i.
                          ****** rewrite <- H_handle_block_finish.
                                 rewrite H_st2'.
                                 simpl.
                                 apply H_len_call_stack.
                          ****** rewrite <- H_handle_block_finish.
                                 rewrite H_st2'.
                                 simpl.
                                 reflexivity.
                          ****** rewrite <- H_handle_block_finish.
                                 rewrite H_st2'.
                                 simpl.
                                 apply H_dialect.
                          ****** exists (top_sf :: hl').
                                 exists tl.
                                 exists sf1.
                                 exists sf2.
                                 repeat split.
                                 ******* rewrite <- H_handle_block_finish.
                                         simpl.
                                         apply H_lt_i.
                                 ******* rewrite <- H_handle_block_finish.
                                         simpl.
                                         apply H_call_stack_st1.
                                 ******* apply H_len_tl_st1.
                                 ******* rewrite H_st2'.
                                         simpl.
                                         rewrite H_call_stack_st2.
                                         simpl.
                                         rewrite length_app.
                                         rewrite Nat.add_comm.
                                         simpl.
                                         rewrite H_call_stack_st1 in H_lt_i.
                                         simpl in H_lt_i.
                                         rewrite length_app in H_lt_i.
                                         rewrite Nat.add_comm in H_lt_i.
                                         simpl in H_lt_i.
                                         apply H_lt_i.
                                 ******* rewrite H_st2'.
                                         simpl.
                                         apply H_call_stack_st2.
                                 ******* apply H_len_tl_st2.
                                 ******* apply H_fname_sf1.
                                 ******* apply H_bid_sf1.
                                 ******* apply H_pc_sf1.
                                 ******* apply H_fname_sf2.
                                 ******* apply H_bid_sf2.
                                 ******* apply H_pc_sf2.
                                 ******* apply H_equiv_assign_sf1_sf2.
                          ****** apply H_live_at_pc.
                          ****** apply H_not_In_v_s.
                    ***** rewrite <- H_handle_block_finish.
                          rewrite H_st2'.
                          unfold equiv_vars_in_top_frame.
                          simpl.
                          rewrite H_call_stack_st1.
                          rewrite H_call_stack_st2.
                          repeat split; try reflexivity.      

           (* block not found *)
           *** remember (SmallStepD.StateD.set_status st2 (Status.Error "Target block not found in the smart contract")) as st2' eqn:H_st2'.
        
               exists st2'.
               exists bid.
               exists b.
               exists pc.
               exists s.
               repeat split.
               **** apply H_b_exists.
               **** left.
                    repeat split.
                    ***** rewrite <- H_handle_block_finish.
                          simpl.
                          apply H_lt_i.
                    ***** rewrite <- H_handle_block_finish.
                          rewrite H_st2'.
                          simpl.
                          apply H_len_call_stack.
                    ***** rewrite <- H_handle_block_finish.
                          rewrite H_st2'.
                          simpl.
                          reflexivity.
                    ***** rewrite <- H_handle_block_finish.
                          rewrite H_st2'.
                          simpl.
                          apply H_dialect.
                    ***** exists (top_sf :: hl').
                          exists tl.
                          exists sf1.
                          exists sf2.
                          repeat split.
                          ****** rewrite <- H_handle_block_finish.
                                 simpl.
                                 apply H_lt_i.
                          ****** rewrite <- H_handle_block_finish.
                                 simpl.
                                 apply H_call_stack_st1.
                          ****** apply H_len_tl_st1.
                          ****** rewrite H_st2'.
                                 simpl.
                                 rewrite H_call_stack_st2.
                                 simpl.
                                 rewrite length_app.
                                 rewrite Nat.add_comm.
                                 simpl.
                                 rewrite H_call_stack_st1 in H_lt_i.
                                 simpl in H_lt_i.
                                 rewrite length_app in H_lt_i.
                                 rewrite Nat.add_comm in H_lt_i.
                                 simpl in H_lt_i.
                                 apply H_lt_i.
                          ****** rewrite H_st2'.
                                 simpl.
                                 apply H_call_stack_st2.
                          ****** apply H_len_tl_st2.
                          ****** apply H_fname_sf1.
                          ****** apply H_bid_sf1.
                          ****** apply H_pc_sf1.
                          ****** apply H_fname_sf2.
                          ****** apply H_bid_sf2.
                          ****** apply H_pc_sf2.
                          ****** apply H_equiv_assign_sf1_sf2.
                    ***** apply H_live_at_pc.
                    ***** apply H_not_In_v_s.
               **** rewrite <- H_handle_block_finish.
                    rewrite H_st2'.
                    unfold equiv_vars_in_top_frame.
                    simpl.
                    rewrite H_call_stack_st1.
                    rewrite H_call_stack_st2.
                    repeat split; try reflexivity.      





           
        (* jump *)
        ** destruct (SmallStepD.SmartContractD.get_block p (SmallStepD.StackFrameD.function_name top_sf) next_bid) as [next_b|].

           (* block found *)
           *** destruct (SmallStepD.apply_renamings (SmallStepD.SmartContractD.BlockD.phi_function next_b (SmallStepD.StackFrameD.curr_block_id top_sf)) top_sf) as [var_assignments'|] eqn:E_renaming.

               **** remember {|
                                Liveness_snd.StateD.call_stack :=
                                  {|
                                    Liveness_snd.StackFrameD.function_name :=
                                      SmallStepD.StackFrameD.function_name top_sf;
                                    Liveness_snd.StackFrameD.variable_assignments := var_assignments';
                                    Liveness_snd.StackFrameD.curr_block_id := next_bid;
                                    Liveness_snd.StackFrameD.pc := 0
                                  |} :: hl' ++ sf2 :: tl;
                        Liveness_snd.StateD.status := Status.Running;
                        Liveness_snd.StateD.dialect_state := SmallStepD.StateD.dialect_state st2
                      |} as st2' eqn:H_st2'.

                    exists st2'.
                    exists bid.
                    exists b.
                    exists pc.
                    exists s.
                    repeat split; try reflexivity.
                    ***** apply H_b_exists.
                    ***** left.
                          repeat split; try reflexivity.
                          ****** rewrite <- H_handle_block_finish.
                                 simpl.
                                 rewrite length_app.
                                 rewrite Nat.add_comm.
                                 simpl.
                                 rewrite H_call_stack_st1 in H_lt_i.
                                 simpl in H_lt_i.
                                 rewrite length_app in H_lt_i.
                                 rewrite Nat.add_comm in H_lt_i.
                                 simpl in H_lt_i.
                                 apply H_lt_i.
                          ****** rewrite <- H_handle_block_finish.
                                 rewrite H_st2'.
                                 simpl.
                                 rewrite length_app.
                                 rewrite length_app.
                                 rewrite Nat.add_comm.
                                 rewrite Nat.add_comm.
                                 simpl.
                                 reflexivity.
                          ****** rewrite <- H_handle_block_finish.
                                 rewrite H_st2'.
                                 simpl.       
                                 reflexivity.
                          ****** rewrite <- H_handle_block_finish.
                                 rewrite H_st2'.
                                 simpl.       
                                 apply H_dialect.
                          ****** exists ({|
                                            Liveness_snd.StackFrameD.function_name :=
                                              SmallStepD.StackFrameD.function_name top_sf;
                                            Liveness_snd.StackFrameD.variable_assignments := var_assignments';
                                            Liveness_snd.StackFrameD.curr_block_id := next_bid;
                                            Liveness_snd.StackFrameD.pc := 0
                                          |} :: hl').
                                 exists tl.
                                 exists sf1.
                                 exists sf2.
                                 repeat split.
                                 ******* rewrite <- H_handle_block_finish.
                                         simpl.
                                         rewrite length_app.
                                         rewrite Nat.add_comm.
                                         simpl.
                                         rewrite H_call_stack_st1 in H_lt_i.
                                         simpl in H_lt_i.
                                         rewrite length_app in H_lt_i.
                                         rewrite Nat.add_comm in H_lt_i.
                                         simpl in H_lt_i.
                                         apply H_lt_i.
                                 ******* rewrite <- H_handle_block_finish.
                                         simpl.
                                         reflexivity.
                                 ******* apply H_len_tl_st1.
                                 ******* rewrite H_st2'.
                                         simpl.
                                         rewrite length_app.
                                         rewrite Nat.add_comm.
                                         simpl.
                                         rewrite H_call_stack_st1 in H_lt_i.
                                         simpl in H_lt_i.
                                         rewrite length_app in H_lt_i.
                                         rewrite Nat.add_comm in H_lt_i.
                                         simpl in H_lt_i.
                                         apply H_lt_i.
                                 ******* rewrite H_st2'.
                                         simpl.
                                         reflexivity.
                                 ******* apply H_len_tl_st2.
                                 ******* apply H_fname_sf1.
                                 ******* apply H_bid_sf1.
                                 ******* apply H_pc_sf1.
                                 ******* apply H_fname_sf2.
                                 ******* apply H_bid_sf2.
                                 ******* apply H_pc_sf2.
                                 ******* apply H_equiv_assign_sf1_sf2.
                          ****** apply H_live_at_pc.
                          ****** apply H_not_In_v_s.
                    ***** rewrite <- H_handle_block_finish.
                          rewrite H_st2'.
                          unfold equiv_vars_in_top_frame.
                          simpl.
                          repeat split; try reflexivity.      

       
               **** remember (SmallStepD.StateD.set_status st2 (Status.Error  "Error while applying phi-function")) as st2' eqn:H_st2'.
        
                    exists st2'.
                    exists bid.
                    exists b.
                    exists pc.
                    exists s.
                    repeat split.
                    ***** apply H_b_exists.
                    ***** left.
                          repeat split.
                          ****** rewrite <- H_handle_block_finish.
                                 simpl.
                                 apply H_lt_i.
                          ****** rewrite <- H_handle_block_finish.
                                 rewrite H_st2'.
                                 simpl.
                                 apply H_len_call_stack.
                          ****** rewrite <- H_handle_block_finish.
                                 rewrite H_st2'.
                                 simpl.
                                 reflexivity.
                          ****** rewrite <- H_handle_block_finish.
                                 rewrite H_st2'.
                                 simpl.
                                 apply H_dialect.
                          ****** exists (top_sf :: hl').
                                 exists tl.
                                 exists sf1.
                                 exists sf2.
                                 repeat split.
                                 ******* rewrite <- H_handle_block_finish.
                                         simpl.
                                         apply H_lt_i.
                                 ******* rewrite <- H_handle_block_finish.
                                         simpl.
                                         apply H_call_stack_st1.
                                 ******* apply H_len_tl_st1.
                                 ******* rewrite H_st2'.
                                         simpl.
                                         rewrite H_call_stack_st2.
                                         simpl.
                                         rewrite length_app.
                                         rewrite Nat.add_comm.
                                         simpl.
                                         rewrite H_call_stack_st1 in H_lt_i.
                                         simpl in H_lt_i.
                                         rewrite length_app in H_lt_i.
                                         rewrite Nat.add_comm in H_lt_i.
                                         simpl in H_lt_i.
                                         apply H_lt_i.
                                 ******* rewrite H_st2'.
                                         simpl.
                                         apply H_call_stack_st2.
                                 ******* apply H_len_tl_st2.
                                 ******* apply H_fname_sf1.
                                 ******* apply H_bid_sf1.
                                 ******* apply H_pc_sf1.
                                 ******* apply H_fname_sf2.
                                 ******* apply H_bid_sf2.
                                 ******* apply H_pc_sf2.
                                 ******* apply H_equiv_assign_sf1_sf2.
                          ****** apply H_live_at_pc.
                          ****** apply H_not_In_v_s.
                    ***** rewrite <- H_handle_block_finish.
                          rewrite H_st2'.
                          unfold equiv_vars_in_top_frame.
                          simpl.
                          rewrite H_call_stack_st1.
                          rewrite H_call_stack_st2.
                          repeat split; try reflexivity.      


           (* block not found *)
           *** remember (SmallStepD.StateD.set_status st2 (Status.Error "Target block not found in the smart contract")) as st2' eqn:H_st2'.
        
               exists st2'.
               exists bid.
               exists b.
               exists pc.
               exists s.
               repeat split.
               **** apply H_b_exists.
               **** left.
                    repeat split.
                    ***** rewrite <- H_handle_block_finish.
                          simpl.
                          apply H_lt_i.
                    ***** rewrite <- H_handle_block_finish.
                          rewrite H_st2'.
                          simpl.
                          apply H_len_call_stack.
                    ***** rewrite <- H_handle_block_finish.
                          rewrite H_st2'.
                          simpl.
                          reflexivity.
                    ***** rewrite <- H_handle_block_finish.
                          rewrite H_st2'.
                          simpl.
                          apply H_dialect.
                    ***** exists (top_sf :: hl').
                          exists tl.
                          exists sf1.
                          exists sf2.
                          repeat split.
                          ****** rewrite <- H_handle_block_finish.
                                 simpl.
                                 apply H_lt_i.
                          ****** rewrite <- H_handle_block_finish.
                                 simpl.
                                 apply H_call_stack_st1.
                          ****** apply H_len_tl_st1.
                          ****** rewrite H_st2'.
                                 simpl.
                                 rewrite H_call_stack_st2.
                                 simpl.
                                 rewrite length_app.
                                 rewrite Nat.add_comm.
                                 simpl.
                                 rewrite H_call_stack_st1 in H_lt_i.
                                 simpl in H_lt_i.
                                 rewrite length_app in H_lt_i.
                                 rewrite Nat.add_comm in H_lt_i.
                                 simpl in H_lt_i.
                                 apply H_lt_i.
                          ****** rewrite H_st2'.
                                 simpl.
                                 apply H_call_stack_st2.
                          ****** apply H_len_tl_st2.
                          ****** apply H_fname_sf1.
                          ****** apply H_bid_sf1.
                          ****** apply H_pc_sf1.
                          ****** apply H_fname_sf2.
                          ****** apply H_bid_sf2.
                          ****** apply H_pc_sf2.
                          ****** apply H_equiv_assign_sf1_sf2.
                    ***** apply H_live_at_pc.
                    ***** apply H_not_In_v_s.
               **** rewrite <- H_handle_block_finish.
                    rewrite H_st2'.
                    unfold equiv_vars_in_top_frame.
                    simpl.
                    rewrite H_call_stack_st1.
                    rewrite H_call_stack_st2.
                    repeat split; try reflexivity.      

           
        (* return *)
        ** (* we split on wether we return to the frame of sf1/sf2 or not *)

          destruct hl' as [|top_sf' hl''] eqn:E_hl'.

          *** (* return to the frame of sf1/sf2 *)
              simpl.
              simpl in H_handle_block_finish.

              rewrite H_fname_sf2.
              rewrite H_bid_sf2.
              rewrite H_pc_sf2.
              rewrite H_fname_sf1 in H_handle_block_finish .
              rewrite H_bid_sf1 in H_handle_block_finish.
              rewrite H_pc_sf1 in H_handle_block_finish.

              simpl in H_call_stack_st1.
              simpl in H_call_stack_st2.
              destruct (SmallStepD.SmartContractD.get_block p fname bid) as [next_b|] eqn:E_next_b.

             (* block found *)
              **** injection H_b_exists as H_b_exists.
                   subst next_b.
                   destruct (nth_error (SmallStepD.BlockD.instructions b) pc) as [instr|] eqn:E_instr.

                  (* instruction found *)
                   ***** destruct (SmallStepD.VariableAssignmentD.assign_all (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) (SmallStepD.eval_sexpr rs top_sf)) as [prev_sf_var_assignment_1|] eqn:E_prev_sf_var_assignment_1.
                         (* assign_all suceeded *)
                         ****** pose proof (assign_all_some (SmallStepD.SmartContractD.BlockD.InstructionD.output instr)  (SmallStepD.eval_sexpr rs top_sf)  (SmallStepD.StackFrameD.variable_assignments sf1)  (SmallStepD.StackFrameD.variable_assignments sf2) prev_sf_var_assignment_1 E_prev_sf_var_assignment_1 ) as [prev_sf_var_assignment_2 E_prev_sf_var_assignment_2].
                                rewrite E_prev_sf_var_assignment_2.

                                assert(H_pc_is_not_at_end := E_instr).
                                apply some_neq_none in H_pc_is_not_at_end.
                                rewrite (nth_error_Some (SmallStepD.BlockD.instructions b) pc) in H_pc_is_not_at_end.

                                assert(H_live_at_pc' := H_live_at_pc).
                                destruct H_live_at_pc' as [fname bid b0 pc s sout H_b0_exists _ H_pc_at_end | fname bid b0 pc s sout instr' H_b0_exists H_live_at_S_pc H_lt_pc H_get_instr' H_sout].

                                
                                (* this case is not applicable since pc is not at the end *)
                                ******* rewrite E_next_b in H_b0_exists.
                                        injection H_b0_exists as H_b0_exists.
                                        subst b0.
                                        rewrite H_pc_at_end in H_pc_is_not_at_end.
                                        contradiction (Nat.lt_irrefl (length (BlockD.instructions b))).
                                        
                                ******* rewrite E_next_b in H_b0_exists.
                                        injection H_b0_exists as H_b0_exists.
                                        subst b0.

                                        rewrite E_instr in  H_get_instr'.
                                        injection H_get_instr' as H_get_instr'.
                                        subst instr'.
                                      
                                        rewrite <- H_dialect.

                                        remember {|
                                            Liveness_snd.StateD.call_stack :=
                                              {|
                                                Liveness_snd.StackFrameD.function_name := fname;
                                                Liveness_snd.StackFrameD.variable_assignments := prev_sf_var_assignment_2;
                                                Liveness_snd.StackFrameD.curr_block_id := bid;
                                                Liveness_snd.StackFrameD.pc := pc + 1
                                              |} :: tl;
                                             Liveness_snd.StateD.status := Status.Running;
                                            Liveness_snd.StateD.dialect_state := SmallStepD.StateD.dialect_state st1
                                          |} as st2' eqn:H_st2'.
 
                                        exists st2'.
                                        exists bid.
                                        exists b.
                                        exists (S pc).
                                        exists s.
                                repeat split.
                                ******** apply E_next_b.
                                ******** (* now we split on wether v in the output variables *)
                                         pose proof (varlist_in_dec (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) v) as H_v_output.
                                         destruct H_v_output as [H_v_in_output | H_v_not_in_output].

                                         ********* right.
                                         
                                                   rewrite <- (assign_all_preserves_eq_up_to_eq (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) (StackFrameD.variable_assignments sf1) (StackFrameD.variable_assignments sf2) v (SmallStepD.eval_sexpr rs top_sf) prev_sf_var_assignment_1 prev_sf_var_assignment_2 H_v_in_output H_equiv_assign_sf1_sf2  E_prev_sf_var_assignment_1 E_prev_sf_var_assignment_2) in H_st2'.
                                                   rewrite H_st2'.
                                                   rewrite <- H_handle_block_finish.
                                                   reflexivity.
                                         ********* left.
                                                   repeat split.
                                                   ********** rewrite <- H_handle_block_finish.
                                                              simpl.
                                                              rewrite H_len_tl_st1.
                                                              apply Nat.lt_succ_diag_r.
                                                   ********** rewrite <- H_handle_block_finish.
                                                              rewrite H_st2'.
                                                              simpl.
                                                              reflexivity.
                                                   ********** rewrite <- H_handle_block_finish.
                                                              rewrite H_st2'.
                                                              simpl.
                                                              reflexivity.
                                                   ********** rewrite <- H_handle_block_finish.
                                                              rewrite H_st2'.
                                                              simpl. 
                                                              reflexivity.
                                                   ********** exists [].
                                                              exists tl.
                                                              exists {|
                                                                  Liveness_snd.StackFrameD.function_name := fname;
                                                                  Liveness_snd.StackFrameD.variable_assignments := prev_sf_var_assignment_1;
                                                                  Liveness_snd.StackFrameD.curr_block_id := bid;
                                                                  Liveness_snd.StackFrameD.pc := pc + 1
                                                                |}.
                                                              exists {|
                                                                  Liveness_snd.StackFrameD.function_name := fname;
                                                                  Liveness_snd.StackFrameD.variable_assignments := prev_sf_var_assignment_2;
                                                                  Liveness_snd.StackFrameD.curr_block_id := bid;
                                                                  Liveness_snd.StackFrameD.pc := pc + 1
                                                                |}.
                                                              repeat split.
                                                              *********** rewrite <- H_handle_block_finish.
                                                                          simpl.
                                                                          rewrite H_len_tl_st1.
                                                                          apply Nat.lt_succ_diag_r.
                                                              *********** rewrite <- H_handle_block_finish.
                                                                          simpl.
                                                                          reflexivity.
                                                              *********** apply H_len_tl_st1.
                                                              *********** rewrite H_st2'.  
                                                                          simpl.
                                                                          rewrite H_len_tl_st2.
                                                                          apply Nat.lt_succ_diag_r.
                                                              *********** rewrite H_st2'.
                                                                          simpl.
                                                                          reflexivity.
                                                              *********** apply  H_len_tl_st2.
                                                              *********** simpl.
                                                                          rewrite Nat.add_comm.
                                                                          simpl.
                                                                          reflexivity.
                                                              *********** simpl.
                                                                          rewrite Nat.add_comm.
                                                                          simpl.
                                                                          reflexivity.
                                                              *********** apply (assign_all_preserves_eq_up_to (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) v (SmallStepD.eval_sexpr rs top_sf) prev_sf_var_assignment_1 prev_sf_var_assignment_2 H_v_not_in_output H_equiv_assign_sf1_sf2 E_prev_sf_var_assignment_1 E_prev_sf_var_assignment_2).
                                                    ********** apply H_live_at_S_pc.
                                                    ********** apply (not_In_v_fwd v s sout instr H_sout H_not_In_v_s H_v_not_in_output).

              ******** rewrite H_st2'.
                       rewrite <- H_handle_block_finish.
                       unfold equiv_vars_in_top_frame.
                       simpl.
                       repeat split.
                       intros v0 s0 H_accessed_vars H_in_v0_s0.           

                       (* wether v in output or not *)
                       pose proof (varlist_in_dec (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) v) as H_v_output.
                       destruct H_v_output as [H_v_in_output | H_v_not_in_output].

                        ********* rewrite (assign_all_preserves_eq_up_to_eq (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) (StackFrameD.variable_assignments sf1) (StackFrameD.variable_assignments sf2) v (SmallStepD.eval_sexpr rs top_sf) prev_sf_var_assignment_1 prev_sf_var_assignment_2 H_v_in_output H_equiv_assign_sf1_sf2  E_prev_sf_var_assignment_1 E_prev_sf_var_assignment_2).
                                   reflexivity.
                        ********* pose proof (not_In_v_fwd v s sout instr H_sout H_not_In_v_s H_v_not_in_output) as H_not_In_v_s'.
                                  pose proof (accessed_var_instr_neq_v p fname bid b (S pc) s0 v0 s v E_next_b H_live_at_S_pc H_not_In_v_s' H_accessed_vars H_in_v0_s0) as H_v0_neq_v.
                               
                                  apply (assign_all_preserves_eq_up_to (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) v (SmallStepD.eval_sexpr rs top_sf) prev_sf_var_assignment_1 prev_sf_var_assignment_2 H_v_not_in_output H_equiv_assign_sf1_sf2  E_prev_sf_var_assignment_1 E_prev_sf_var_assignment_2 v0 H_v0_neq_v).

                         (* assign_all failed *)
                         ****** rewrite (assign_all_none (SmallStepD.SmartContractD.BlockD.InstructionD.output instr)  (SmallStepD.eval_sexpr rs top_sf)  (SmallStepD.StackFrameD.variable_assignments sf1)  (SmallStepD.StackFrameD.variable_assignments sf2) E_prev_sf_var_assignment_1 ).
                                remember (SmallStepD.StateD.set_status st2 (Status.Error "Failed to assign return values")) as st2' eqn:H_st2'.
        
                                exists st2'.
                                exists bid.
                                exists b.
                                exists pc.
                                exists s.
                                repeat split.
                                ******* apply E_next_b.
                                ******* left.
                                        repeat split.
                                        ******** rewrite <- H_handle_block_finish.
                                                 simpl.
                                                 apply H_lt_i.
                                        ******** rewrite <- H_handle_block_finish.
                                                 rewrite H_st2'.
                                                 simpl.
                                                 apply H_len_call_stack.
                                        ******** rewrite <- H_handle_block_finish.
                                                 rewrite H_st2'.
                                                 simpl.
                                                 reflexivity.
                                        ******** rewrite <- H_handle_block_finish.
                                                 rewrite H_st2'.
                                                 simpl.
                                                 apply H_dialect.
                                        ******** exists [top_sf].
                                                 exists tl.
                                                 exists sf1.
                                                 exists sf2.
                                                 repeat split.
                                                 ********* rewrite <- H_handle_block_finish.
                                                           simpl.
                                                           apply H_lt_i.
                                                 ********* rewrite <- H_handle_block_finish.
                                                           simpl.
                                                           apply H_call_stack_st1.
                                                 ********* apply H_len_tl_st1.
                                                 ********* rewrite H_st2'.
                                                           simpl.
                                                           rewrite H_call_stack_st2.
                                                           simpl.
                                                           rewrite H_len_tl_st2.
                                                           apply i_SS_i.
                                                 ********* rewrite H_st2'.
                                                           simpl.
                                                           apply H_call_stack_st2.
                                                 ********* apply H_len_tl_st2.
                                                 ********* apply H_fname_sf1.
                                                 ********* apply H_bid_sf1.
                                                 ********* apply H_pc_sf1.
                                                 ********* apply H_fname_sf2.
                                                 ********* apply H_bid_sf2.
                                                 ********* apply H_pc_sf2.
                                                 ********* apply H_equiv_assign_sf1_sf2.
                                        ******** apply H_live_at_pc.
                                        ******** apply H_not_In_v_s.
                                ******* rewrite <- H_handle_block_finish.
                                       rewrite H_st2'.
                                       unfold equiv_vars_in_top_frame.
                                       simpl.
                                       rewrite H_call_stack_st1.
                                       rewrite H_call_stack_st2.
                                       repeat split; try reflexivity.      


                  (* instruction not found *)
                   ***** remember (SmallStepD.StateD.set_status st2 (Status.Error "Failed to find call instruction")) as st2' eqn:H_st2'.
        
                          exists st2'.
                          exists bid.
                          exists b.
                          exists pc.
                          exists s.
                          repeat split.
                         ****** apply E_next_b.
                         ****** left.
                                  repeat split.
                                 ******* rewrite <- H_handle_block_finish.
                                           simpl.
                                           apply H_lt_i.
                                 ******* rewrite <- H_handle_block_finish.
                                           rewrite H_st2'.
                                           simpl.
                                           apply H_len_call_stack.
                                 ******* rewrite <- H_handle_block_finish.
                                           rewrite H_st2'.
                                           simpl.
                                           reflexivity.
                                 ******* rewrite <- H_handle_block_finish.
                                           rewrite H_st2'.
                                           simpl.
                                           apply H_dialect.
                                 ******* exists [top_sf].
                                         exists tl.
                                         exists sf1.
                                         exists sf2.
                                         repeat split.
                                         ******** rewrite <- H_handle_block_finish.
                                                  simpl.
                                                  apply H_lt_i.
                                         ******** rewrite <- H_handle_block_finish.
                                                  simpl.
                                                  apply H_call_stack_st1.
                                         ******** apply H_len_tl_st1.
                                         ******** rewrite H_st2'.
                                                    simpl.
                                                    rewrite H_call_stack_st2.
                                                    simpl.
                                                    rewrite H_len_tl_st2.
                                                    apply i_SS_i.
                                          ******** rewrite H_st2'.
                                                   simpl.
                                                   apply H_call_stack_st2.
                                          ******** apply H_len_tl_st2.
                                          ******** apply H_fname_sf1.
                                          ******** apply H_bid_sf1.
                                          ******** apply H_pc_sf1.
                                          ******** apply H_fname_sf2.
                                          ******** apply H_bid_sf2.
                                          ******** apply H_pc_sf2.
                                          ******** apply H_equiv_assign_sf1_sf2.
                                 ******* apply H_live_at_pc.
                                 ******* apply H_not_In_v_s.
                         ****** rewrite <- H_handle_block_finish.
                                  rewrite H_st2'.
                                  unfold equiv_vars_in_top_frame.
                                  simpl.
                                  rewrite H_call_stack_st1.
                                  rewrite H_call_stack_st2.
                                  repeat split; try reflexivity.      

                   
             (* block not found *)
              **** discriminate H_b_exists.

                
          *** (* return to the frame above of sf1/sf2 -- easy case*)
              rewrite <- app_comm_cons.
              rewrite <- app_comm_cons in H_handle_block_finish.
              
              destruct (SmallStepD.SmartContractD.get_block p (SmallStepD.StackFrameD.function_name top_sf') (SmallStepD.StackFrameD.curr_block_id top_sf')) as [next_b|] eqn:E_next_b.

             (* block found *)
              **** destruct (nth_error (SmallStepD.BlockD.instructions next_b) (SmallStepD.StackFrameD.pc top_sf')) as [instr|] eqn:E_instr.
                   (* instruction found *)
                   ***** destruct (SmallStepD.VariableAssignmentD.assign_all (SmallStepD.StackFrameD.variable_assignments top_sf') (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) (SmallStepD.eval_sexpr rs top_sf)) as [prev_sf_var_assignment'|] eqn:E_prev_sf_var_assignment'.

                   (* assign_all success *)
                   ****** remember {|
                                      Liveness_snd.StateD.call_stack :=
                                       {|
                                         Liveness_snd.StackFrameD.function_name := SmallStepD.StackFrameD.function_name top_sf';
                                         Liveness_snd.StackFrameD.variable_assignments := prev_sf_var_assignment';
                                         Liveness_snd.StackFrameD.curr_block_id := SmallStepD.StackFrameD.curr_block_id top_sf';
                                         Liveness_snd.StackFrameD.pc := SmallStepD.StackFrameD.pc top_sf' + 1
                                       |} :: hl'' ++ sf2 :: tl;
                              Liveness_snd.StateD.status := Status.Running;
                              Liveness_snd.StateD.dialect_state := SmallStepD.StateD.dialect_state st2
                            |} as st2' eqn:H_st2'.
 
                          exists st2'.
                          exists bid.
                          exists b.
                          exists pc.
                          exists s.
                          repeat split; try reflexivity.
                          ******* apply H_b_exists.
                          ******* left.
                                  repeat split; try reflexivity.
                                  ******** rewrite <- H_handle_block_finish.
                                           simpl.
                                           rewrite length_app.
                                           rewrite Nat.add_comm.
                                           simpl.
                                           rewrite H_len_tl_st1.
                                           apply i_SS_i_p.
                                  ******** rewrite <- H_handle_block_finish.
                                           rewrite H_st2'.
                                           simpl.
                                           rewrite length_app.
                                           rewrite length_app.
                                           rewrite Nat.add_comm.
                                           rewrite Nat.add_comm.
                                           simpl.
                                           reflexivity.
                                  ******** rewrite <- H_handle_block_finish.
                                           rewrite H_st2'.
                                           simpl.       
                                           reflexivity.
                                  ******** rewrite <- H_handle_block_finish.
                                           rewrite H_st2'.
                                           simpl.       
                                           apply H_dialect.
                                  ******** exists ({|
                                                      Liveness_snd.StackFrameD.function_name := SmallStepD.StackFrameD.function_name top_sf';
                                                      Liveness_snd.StackFrameD.variable_assignments := prev_sf_var_assignment';
                                                      Liveness_snd.StackFrameD.curr_block_id := SmallStepD.StackFrameD.curr_block_id top_sf';
                                                      Liveness_snd.StackFrameD.pc := SmallStepD.StackFrameD.pc top_sf' + 1
                                                    |} :: hl'').
                                           exists tl.
                                           exists sf1.
                                           exists sf2.
                                           repeat split.
                                           ********* rewrite <- H_handle_block_finish.
                                                     simpl.
                                                     rewrite length_app.
                                                     rewrite Nat.add_comm.
                                                     simpl.
                                                     rewrite H_len_tl_st1.
                                                     apply i_SS_i_p.
                                           ********* rewrite <- H_handle_block_finish.
                                                     simpl.
                                                     reflexivity.
                                           ********* apply H_len_tl_st1.
                                           ********* rewrite H_st2'.
                                                     simpl.
                                                     rewrite length_app.
                                                     rewrite Nat.add_comm.
                                                     simpl.
                                                     rewrite H_len_tl_st1.
                                                     apply i_SS_i_p.
                                           ********* rewrite H_st2'.
                                                     simpl.
                                                     reflexivity.
                                           ********* apply H_len_tl_st2.
                                           ********* apply H_fname_sf1.
                                           ********* apply H_bid_sf1.
                                           ********* apply H_pc_sf1.
                                           ********* apply H_fname_sf2.
                                           ********* apply H_bid_sf2.
                                           ********* apply H_pc_sf2.
                                           ********* apply H_equiv_assign_sf1_sf2.
                                  ******** apply H_live_at_pc.
                                  ******** apply H_not_In_v_s.
                          ******* rewrite <- H_handle_block_finish.
                                  rewrite H_st2'.
                                  unfold equiv_vars_in_top_frame.
                                  simpl.
                                  repeat split; try reflexivity.      

                     
                   (* assign_all fail *)
                   ****** remember (SmallStepD.StateD.set_status st2 (Status.Error "Failed to assign return values")) as st2' eqn:H_st2'.
        
                          exists st2'.
                          exists bid.
                          exists b.
                          exists pc.
                          exists s.
                          repeat split.
                          ******* apply H_b_exists.
                          ******* left.
                                  repeat split.
                                  ******** rewrite <- H_handle_block_finish.
                                           simpl.
                                           apply H_lt_i.
                                  ******** rewrite <- H_handle_block_finish.
                                           rewrite H_st2'.
                                           simpl.
                                           apply H_len_call_stack.
                                  ******** rewrite <- H_handle_block_finish.
                                           rewrite H_st2'.
                                           simpl.
                                           reflexivity.
                                  ******** rewrite <- H_handle_block_finish.
                                           rewrite H_st2'.
                                           simpl.
                                           apply H_dialect.
                                  ******** exists (top_sf :: (top_sf' :: hl'')).
                                           exists tl.
                                           exists sf1.
                                           exists sf2.
                                           repeat split.
                                           ********* rewrite <- H_handle_block_finish.
                                                     simpl.
                                                     apply H_lt_i.
                                           ********* rewrite <- H_handle_block_finish.
                                                     simpl.
                                                     apply H_call_stack_st1.
                                           ********* apply H_len_tl_st1.
                                           ********* rewrite H_st2'.
                                                     simpl.
                                                     rewrite H_call_stack_st2.
                                                     simpl.
                                                     rewrite length_app.
                                                     rewrite Nat.add_comm.
                                                     simpl.
                                                     rewrite H_call_stack_st1 in H_lt_i.
                                                     simpl in H_lt_i.
                                                     rewrite length_app in H_lt_i.
                                                     rewrite Nat.add_comm in H_lt_i.
                                                     simpl in H_lt_i.
                                                     apply H_lt_i.
                                           ********* rewrite H_st2'.
                                                     simpl.
                                                     apply H_call_stack_st2.
                                           ********* apply H_len_tl_st2.
                                           ********* apply H_fname_sf1.
                                           ********* apply H_bid_sf1.
                                           ********* apply H_pc_sf1.
                                           ********* apply H_fname_sf2.
                                           ********* apply H_bid_sf2.
                                           ********* apply H_pc_sf2.
                                           ********* apply H_equiv_assign_sf1_sf2.
                                  ******** apply H_live_at_pc.
                                  ******** apply H_not_In_v_s.
                          ******* rewrite <- H_handle_block_finish.
                                  rewrite H_st2'.
                                  unfold equiv_vars_in_top_frame.
                                  simpl.
                                  rewrite H_call_stack_st1.
                                  rewrite H_call_stack_st2.
                                  repeat split; try reflexivity.      

                   (* instruction not found *)
                   ***** remember (SmallStepD.StateD.set_status st2 (Status.Error "Failed to find call instruction")) as st2' eqn:H_st2'.
        
                          exists st2'.
                          exists bid.
                          exists b.
                          exists pc.
                          exists s.
                          repeat split.
                         ****** apply H_b_exists.
                         ****** left.
                                  repeat split.
                                 ******* rewrite <- H_handle_block_finish.
                                           simpl.
                                           apply H_lt_i.
                                 ******* rewrite <- H_handle_block_finish.
                                           rewrite H_st2'.
                                           simpl.
                                           apply H_len_call_stack.
                                 ******* rewrite <- H_handle_block_finish.
                                           rewrite H_st2'.
                                           simpl.
                                           reflexivity.
                                 ******* rewrite <- H_handle_block_finish.
                                           rewrite H_st2'.
                                           simpl.
                                           apply H_dialect.
                                 ******* exists (top_sf :: (top_sf' :: hl'')).
                                           exists tl.
                                           exists sf1.
                                           exists sf2.
                                           repeat split.
                                          ******** rewrite <- H_handle_block_finish.
                                                     simpl.
                                                     apply H_lt_i.
                                          ******** rewrite <- H_handle_block_finish.
                                                     simpl.
                                                     apply H_call_stack_st1.
                                          ******** apply H_len_tl_st1.
                                          ******** rewrite H_st2'.
                                                     simpl.
                                                     rewrite H_call_stack_st2.
                                                     simpl.
                                                     rewrite length_app.
                                                     rewrite Nat.add_comm.
                                                     simpl.
                                                     rewrite H_call_stack_st1 in H_lt_i.
                                                     simpl in H_lt_i.
                                                     rewrite length_app in H_lt_i.
                                                     rewrite Nat.add_comm in H_lt_i.
                                                     simpl in H_lt_i.
                                                     apply H_lt_i.
                                          ******** rewrite H_st2'.
                                                     simpl.
                                                     apply H_call_stack_st2.
                                          ******** apply H_len_tl_st2.
                                          ******** apply H_fname_sf1.
                                          ******** apply H_bid_sf1.
                                          ******** apply H_pc_sf1.
                                          ******** apply H_fname_sf2.
                                          ******** apply H_bid_sf2.
                                          ******** apply H_pc_sf2.
                                          ******** apply H_equiv_assign_sf1_sf2.
                                 ******* apply H_live_at_pc.
                                 ******* apply H_not_In_v_s.
                         ****** rewrite <- H_handle_block_finish.
                                  rewrite H_st2'.
                                  unfold equiv_vars_in_top_frame.
                                  simpl.
                                  rewrite H_call_stack_st1.
                                  rewrite H_call_stack_st2.
                                  repeat split; try reflexivity.      


              (* block not found *)
              **** remember (SmallStepD.StateD.set_status st2 (Status.Error "Failed to calling block")) as st2' eqn:H_st2'.
        
                   exists st2'.
                   exists bid.
                   exists b.
                   exists pc.
                   exists s.
                   repeat split.
                   ***** apply H_b_exists.
                   ***** left.
                         repeat split.
                         ****** rewrite <- H_handle_block_finish.
                                simpl.
                                apply H_lt_i.
                         ****** rewrite <- H_handle_block_finish.
                                rewrite H_st2'.
                                simpl.
                                apply H_len_call_stack.
                         ****** rewrite <- H_handle_block_finish.
                                rewrite H_st2'.
                                simpl.
                                reflexivity.
                         ****** rewrite <- H_handle_block_finish.
                                rewrite H_st2'.
                                simpl.
                                apply H_dialect.
                         ****** exists (top_sf :: (top_sf' :: hl'')).
                                exists tl.
                                exists sf1.
                                exists sf2.
                                repeat split.
                                ******* rewrite <- H_handle_block_finish.
                                        simpl.
                                        apply H_lt_i.
                                ******* rewrite <- H_handle_block_finish.
                                        simpl.
                                        apply H_call_stack_st1.
                                ******* apply H_len_tl_st1.
                                ******* rewrite H_st2'.
                                        simpl.
                                        rewrite H_call_stack_st2.
                                        simpl.
                                        rewrite length_app.
                                        rewrite Nat.add_comm.
                                        simpl.
                                        rewrite H_call_stack_st1 in H_lt_i.
                                        simpl in H_lt_i.
                                        rewrite length_app in H_lt_i.
                                        rewrite Nat.add_comm in H_lt_i.
                                        simpl in H_lt_i.
                                        apply H_lt_i.
                                ******* rewrite H_st2'.
                                        simpl.
                                        apply H_call_stack_st2.
                                ******* apply H_len_tl_st2.
                                ******* apply H_fname_sf1.
                                ******* apply H_bid_sf1.
                                ******* apply H_pc_sf1.
                                ******* apply H_fname_sf2.
                                ******* apply H_bid_sf2.
                                ******* apply H_pc_sf2.
                                ******* apply H_equiv_assign_sf1_sf2.
                         ****** apply H_live_at_pc.
                         ****** apply H_not_In_v_s.
                   ***** rewrite <- H_handle_block_finish.
                         rewrite H_st2'.
                         unfold equiv_vars_in_top_frame.
                         simpl.
                         rewrite H_call_stack_st1.
                         rewrite H_call_stack_st2.
                         repeat split; try reflexivity.      



        (* terminated *)
        ** remember (SmallStepD.StateD.set_status st2 Status.Terminated) as st2' eqn:H_st2'.
           exists st2'.
           exists bid.
           exists b.
           exists pc.
           exists s.
           repeat split.
           *** apply H_b_exists.
           *** left.
               repeat split.
               **** rewrite <- H_handle_block_finish.
                    simpl.
                    apply H_lt_i.
               **** rewrite <- H_handle_block_finish.
                    rewrite H_st2'.
                    simpl.
                    apply H_len_call_stack.
               **** rewrite <- H_handle_block_finish.
                    rewrite H_st2'.
                    simpl.
                    reflexivity.
               **** rewrite <- H_handle_block_finish.
                    rewrite H_st2'.
                    simpl.
                    apply H_dialect.
               **** exists (top_sf :: hl').
                    exists tl.
                    exists sf1.
                    exists sf2.
                    repeat split.
                    ***** rewrite <- H_handle_block_finish.
                          simpl.
                          apply H_lt_i.
                    ***** rewrite <- H_handle_block_finish.
                          simpl.
                          apply H_call_stack_st1.
                    ***** apply H_len_tl_st1.
                    ***** rewrite H_st2'.
                          simpl.
                          rewrite H_call_stack_st2.
                          simpl.
                          rewrite H_call_stack_st1 in H_lt_i.
                          simpl in H_lt_i.
                          rewrite length_app in H_lt_i.
                          rewrite Nat.add_comm in H_lt_i.
                          simpl in H_lt_i.                        
                          rewrite length_app.
                          rewrite Nat.add_comm.
                          simpl.
                          apply H_lt_i.
                    ***** rewrite H_st2'.
                          simpl.
                          apply H_call_stack_st2.
                    ***** apply H_len_tl_st2.
                    ***** apply H_fname_sf1.
                    ***** apply H_bid_sf1.
                    ***** apply H_pc_sf1.
                    ***** apply H_fname_sf2.
                    ***** apply H_bid_sf2.
                    ***** apply H_pc_sf2.
                    ***** apply H_equiv_assign_sf1_sf2.
               **** apply H_live_at_pc.
               **** apply H_not_In_v_s.
           *** rewrite <- H_handle_block_finish.
               rewrite H_st2'.
               unfold equiv_vars_in_top_frame.
               simpl.
               rewrite H_call_stack_st1.
               rewrite H_call_stack_st2.
               repeat split; try reflexivity.

      (* block not found *)
      * remember (SmallStepD.StateD.set_status st2 (Status.Error "Current block not found in the smart contract")) as st2' eqn:H_st2'.
        
        exists st2'.
        exists bid.
        exists b.
        exists pc.
        exists s.
        repeat split.
        ** apply H_b_exists.
        ** left.
           repeat split.
           *** rewrite <- H_handle_block_finish.
               simpl.
               apply H_lt_i.
           *** rewrite <- H_handle_block_finish.
               rewrite H_st2'.
               simpl.
               apply H_len_call_stack.
           *** rewrite <- H_handle_block_finish.
               rewrite H_st2'.
               simpl.
               reflexivity.
           *** rewrite <- H_handle_block_finish.
               rewrite H_st2'.
               simpl.
               apply H_dialect.
           *** exists (top_sf :: hl').
               exists tl.
               exists sf1.
               exists sf2.
               repeat split.
               **** rewrite <- H_handle_block_finish.
                    simpl.
                    apply H_lt_i.
               **** rewrite <- H_handle_block_finish.
                    simpl.
                    apply H_call_stack_st1.
               **** apply H_len_tl_st1.
               **** rewrite H_st2'.
                    simpl.
                    rewrite H_call_stack_st2.
                    simpl.
                    rewrite length_app.
                    rewrite Nat.add_comm.
                    simpl.
                    rewrite H_call_stack_st1 in H_lt_i.
                    simpl in H_lt_i.
                    rewrite length_app in H_lt_i.
                    rewrite Nat.add_comm in H_lt_i.
                    simpl in H_lt_i.
                    apply H_lt_i.
               **** rewrite H_st2'.
                    simpl.
                    apply H_call_stack_st2.
               **** apply H_len_tl_st2.
               **** apply H_fname_sf1.
               **** apply H_bid_sf1.
               **** apply H_pc_sf1.
               **** apply H_fname_sf2.
               **** apply H_bid_sf2.
               **** apply H_pc_sf2.
               **** apply H_equiv_assign_sf1_sf2.
           *** apply H_live_at_pc.
           *** apply H_not_In_v_s.
        ** rewrite <- H_handle_block_finish.
           rewrite H_st2'.
           unfold equiv_vars_in_top_frame.
           simpl.
           rewrite H_call_stack_st1.
           rewrite H_call_stack_st2.
           repeat split; try reflexivity.      
Qed.


  
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
        
        apply (live_at_exec_inst_snd p i fname bid b pc s instr H_exists_b H_live_at_pc st1 st2 st1' v H_equiv_up_to_i_v_st1_st2 E_get_instr_st1 H_step_st1 H_not_In_v_s ).
        
      + pose proof (get_next_instr_eq_states p i fname bid pc v st1 st2 H_equiv_up_to_i_v_st1_st2) as H_get_instr_st2.
        rewrite E_get_instr_st1 in H_get_instr_st2.
        rewrite <- H_get_instr_st2.
        
        apply (live_at_handle_block_finish_snd p i fname bid b pc s H_exists_b H_live_at_pc st1 st2 st1' v H_equiv_up_to_i_v_st1_st2 E_get_instr_st1 H_step_st1 H_not_In_v_s ).
        
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
        apply (equiv_state_equiv_frames_at_top p fname bid b pc i v s st1 st2 H_b_exists H_live_at_pc H_not_In_v_s H_equiv_st1_st2).

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

End Liveness_snd.

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
