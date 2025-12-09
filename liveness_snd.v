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
Require Import stdpp.relations.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Lia.


Module Liveness_snd (D: DIALECT).

  Module LivenessD := Liveness(D).
  Module SmallStepD := LivenessD.SmallStepD.
  Module StateD := SmallStepD.StateD.
  Module CallStackD := StateD.CallStackD.
  Module StackFrameD := CallStackD.StackFrameD.
  Module LocalsD := StackFrameD.LocalsD.
  Module CFGProgD := CFGProg(D).
  Module CFGFunD := CFGProgD.CFGFunD.
  Module BlockD := CFGProgD.BlockD.
  Module PhiInfoD := BlockD.PhiInfoD.
  Module InstrD := BlockD.InstrD.
  Module ExitInfoD := BlockD.ExitInfoD.
  Module SimpleExprD := ExitInfoD.SimpleExprD.
  Module DialectFactsD := DialectFacts(D).
  
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

    
  (* helper lemma to rewite between Some and not equal None *)
  Lemma some_iff_neq_none {A: Type}:
    forall (x: option A),
      (exists y, x = Some y) <-> x <> None.
  Proof.
    intros x.
    split.
    - intros H.
      destruct H as [y H].
      subst.
      intros H_contra.
      discriminate.
    - intros H.
      destruct x as [y|]; try contradiction.
      exists y.
      reflexivity.
  Qed.

  (* yet another helper lemma to rewite between Some and not equal
  None *)
  Lemma some_implies_neq_none {A: Type}:
    forall (x: option A) (y: A),
      x = Some y -> x <> None.
  Proof.
    intros x y.
    intro H.
    intro H_contra.
    subst.
    discriminate.
  Qed.

  (* nth_error succeed when applied to a valid index *)
  Lemma valid_index_nth_error {A : Type}:
    forall (n : nat) (l : list A),
      n < length l -> exists y, nth_error l n = Some y.
  Proof.
  intros n l H_lt.
  apply nth_error_Some in H_lt.
  destruct (nth_error l n) eqn:E_val. 
  - exists a. reflexivity.
  - contradiction.
  Qed.

  (* some logical equivalence of forall of negated disjuction *)
  Lemma forall_not_or_dist : forall (A : Type) (P1 P2 : A -> Prop),
      (forall x, ~(P1 x \/ P2 x)) <-> ((forall x, ~P1 x) /\ (forall x, ~P2 x)).
  Proof.
    intros. split.
    - intros H. split; intros x Hx; apply (H x).
      + left. exact Hx.
      + right. exact Hx.
    - intros [H1 H2] x [HP1 | HP2].
      + apply (H1 x). exact HP1.
      + apply (H2 x). exact HP2.
  Qed.

  (*TBD: most likely obsolete *)
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

  (*TBD: most likely obsolete *)
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

  Lemma varid_eq_or_neq:
    forall (x y: VarID.t), x=y \/ x<>y.
  Proof.
    intros x y.
    destruct (VarID.eqb x y) eqn:E_xy.
    - rewrite VarID.eqb_eq in E_xy.
      left.
      apply E_xy.
    - rewrite VarID.eqb_neq_false in E_xy.
      right.
      apply E_xy.
  Qed.

  Lemma blockid_eq_or_neq:
    forall (x y: BlockID.t), x=y \/ x<>y.
  Proof.
    intros x y.
    destruct (BlockID.eqb x y) eqn:E_xy.
    - rewrite BlockID.eqb_eq in E_xy.
      left.
      apply E_xy.
    - rewrite BlockID.eqb_neq_false in E_xy.
      right.
      apply E_xy.
  Qed.

  (* The specification of function [list_to_set] *)
  Lemma list_to_set_spec:
    forall l v,
      List.In v l <-> VarSet.In v (list_to_set l).
  Proof.
    induction l as [|a l' IHl'].
    - intro v.
      simpl.
      split; try contradiction.
      + intros.
        pose proof (VarSet.empty_spec) as H_empty.
        unfold VarSet.Empty in H_empty.
        contradiction (H_empty v).
    - intro v.
      split.
      + intro H_In_v_a_cons_l'.
        simpl in H_In_v_a_cons_l'.
        destruct H_In_v_a_cons_l' as [H_v_eq_a | H_In_l'].
        * simpl.
          rewrite VarSet.add_spec.
          left.
          symmetry.
          apply H_v_eq_a.
        * simpl.
          rewrite VarSet.add_spec.
          right.
          apply IHl'.
          apply H_In_l'.
      + intro H_In_v_a_toset_l'.
        simpl in H_In_v_a_toset_l'.
        rewrite VarSet.add_spec in H_In_v_a_toset_l'. 
        destruct H_In_v_a_toset_l' as [H_v_eq_a | H_In_toset_l'].
        * simpl.
          left.
          symmetry.
          apply H_v_eq_a.
        * simpl.
          right.
          apply IHl'.
          apply H_In_toset_l'.
  Qed.

  
  (* The specification of function [extract_yul_vars] *)
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
      + intro H_In_inl_v_a_cons_l'.
        simpl in H_In_inl_v_a_cons_l'.
        destruct H_In_inl_v_a_cons_l' as [H_inl_v_eq_a | H_In_inl_v_l'].
        * destruct a; try discriminate.
          simpl.
          left.
          injection H_inl_v_eq_a as H_inlv_eq_a.
          apply H_inlv_eq_a.
        * destruct a.
          ** simpl.
             right.
             apply IHl'.
             apply H_In_inl_v_l'.
          ** simpl.
             apply IHl'.
             apply H_In_inl_v_l'.
      + intro H_In_v_ex_a_l'.
        destruct a as [var | val].
        * simpl in H_In_v_ex_a_l'.
          destruct H_In_v_ex_a_l' as [H_var_eq_v | H_In_v_ex_l'].
          ** simpl.
             left.
             rewrite H_var_eq_v.
             reflexivity.
          ** simpl.
             right.
             apply IHl'.
             apply  H_In_v_ex_l'.
        * simpl in H_In_v_ex_a_l'.
          simpl.
          right.
          apply IHl'.
          apply H_In_v_ex_a_l'.
  Qed.

  (* VarSet.remove produces equal sets when applied to equal sets *)
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

  (* VarSet.add produce equal sets when applied to equal sets *)
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

  (* VarSet.mem produces equal sets when applied to equal sets *)
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

  (* VarSet.diff produces equal sets when applied to equal sets *)
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

  (* VarSet.union produces equal sets when applied to equal sets *)
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

  (* VarSet.In is preserved for equal sets *)
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

  (* ~VarSet.In is preserved for equal sets *)
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

  (* If [x] is in [s] and [y] is not then [x<>y] *)
  Lemma not_In_neq:
    forall x y s,
      VarSet.In x s ->
      ~VarSet.In y s ->
      x<>y.
  Proof.
    intros x y s H_xs H_ys.
    congruence.
  Qed.

  (* VarSet.Equal is reflexive *)
  Lemma varset_equal_refl:
    forall s,
      VarSet.Equal s s.
  Proof.
    intro s.
    unfold VarSet.Equal.
    intros x.
    reflexivity.
  Qed.

  (* VarSet.Equal is symmetric --- it must be in the library since Equal is an equivalence relation *)
  Lemma varset_equal_sym:
    forall s1 s2,
      VarSet.Equal s1 s2 <-> VarSet.Equal s2 s1.
  Proof.
    intros s1 s2.
    split.
    - intro H_s1_eq_s2.
      unfold VarSet.Equal in *.
      intros a.
      rewrite H_s1_eq_s2.
      reflexivity.
    - intro H_s2_eq_s1.
      unfold VarSet.Equal in *.
      intros a.
      rewrite H_s2_eq_s1.
      reflexivity.
  Qed.
  
  (* VarSet.Equal is transitive --- it must be in the library since Equal is an equivalence relation *)
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

  (* [apply_inv_phi] produces equal sets when applied to equal sets *)
  Lemma apply_inv_phi_preserves_equal:
    forall l s1 s2,
      VarSet.Equal s1 s2 ->
      VarSet.Equal (apply_inv_phi l s1) (apply_inv_phi l s2).
  Proof.
    intros l s1 s2 H_eq_s1_s2.
    unfold apply_inv_phi.
    destruct l as [out_vars in_sexprs _ _].
    remember (list_to_set out_vars) as outset eqn:E_outset.
    remember (list_to_set (extract_yul_vars in_sexprs)) as inset eqn:E_inset.

    pose proof (diff_preserves_equal s1 s2 outset outset H_eq_s1_s2 (varset_equal_refl outset)) as H_diff.

    apply (union_preserves_equal (VarSet.diff s1 outset) (VarSet.diff s2 outset) inset inset H_diff (varset_equal_refl inset)).
  Qed.
      

  
  (* If the length of a list is not 0, then it can be destructed to head and tail *)
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

  (* [prop_live_set_bkw_instr] produces equal sets when applied to equal sets *)
  Lemma prop_live_set_bkw_instr_preserves_equal:
    forall i s1 s2,
      VarSet.Equal s1 s2 ->
      VarSet.Equal (prop_live_set_bkw_instr i s1) (prop_live_set_bkw_instr i s2).
  Proof.
    intros i s1 s2 H_s1_eq_s2.
    unfold prop_live_set_bkw_instr.
    apply  (union_preserves_equal (VarSet.diff s1 (list_to_set i.(output))) (VarSet.diff s2 (list_to_set i.(output))) (list_to_set (extract_yul_vars i.(input))) (list_to_set (extract_yul_vars i.(input))) (diff_preserves_equal s1 s2 (list_to_set i.(output)) (list_to_set i.(output)) H_s1_eq_s2 (varset_equal_refl (list_to_set i.(output)))) (varset_equal_refl  (list_to_set (extract_yul_vars i.(input))))).
  Qed.

  (* [prop_live_set_bkw_aux_instr] produces equal sets when applied to equal sets *)
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

  (* for rewriintg between [prop_live_set_bkw] and [prop_live_set_bkw_aux] which is trivial, but unfold unfolds too much *)
  Lemma prop_live_set_bkw_is_prop_aux:
    forall l s,
      prop_live_set_bkw l s = prop_live_set_bkw_aux (length l) (rev l) s.
  Proof.
    intros l s.
    destruct l as [|i l'] eqn:E_l.
    - simpl. reflexivity.
    - unfold prop_live_set_bkw. reflexivity.
  Qed.

  (* [prop_live_set_bkw] produces equal sets when applied to equal sets *)
  Lemma prop_live_set_bkw_preserves_equal:
    forall l s1 s2,
      VarSet.Equal s1 s2 ->
      VarSet.Equal (prop_live_set_bkw l s1) (prop_live_set_bkw l s2).
  Proof.
    intros l s1 s2 H_eq_s1_s2.
    repeat rewrite prop_live_set_bkw_is_prop_aux.
    apply (prop_live_set_bkw_aux_preserves_equal (Datatypes.length l) (rev l) s1 s2 H_eq_s1_s2).
  Qed.

 
  (*
    The following co-inductive defintions are for live variables properties,
    they coincide with the equations that we explianed in liveness.v
    
    - live_out p fname bid s: s is the set of live variables at the exit of the block p/fname/bid
    - live_in p fname bid s: s is the set of live variables at the entry of the block p/fname/bid
  *)
  CoInductive live_out  (p : CFGProgD.t) : FuncName.t -> BlockID.t -> VarSet.t -> Prop :=

  (* Return block *)
  | lo_block_w_ret (fname : FuncName.t) (bid :  BlockID.t) (b: BlockD.t) (rs: list SimpleExprD.t) (sout: VarSet.t):
    CFGProgD.get_block p fname bid = Some b -> (* the block exists *)
    BlockD.is_return_block b = Some rs -> (* it is an exit block and rs is the list of returned expressions *)
    VarSet.Equal sout (list_to_set (extract_yul_vars rs)) ->
    live_out p fname bid sout

  (* Terminate block *)
  | lo_block_w_ter (fname : FuncName.t) (bid :  BlockID.t) (b: BlockD.t) (sout: VarSet.t) :
    CFGProgD.get_block p fname bid = Some b -> (* the block exists *)
    BlockD.is_terminated_block b = true -> (* it is an terminate block *)
    VarSet.Equal sout VarSet.empty ->
    live_out p fname bid sout

  (* A block with a with jump *)
  | lo_block_w_jump (fname : FuncName.t) (bid next_bid:  BlockID.t) (b next_b: BlockD.t) (s: VarSet.t) (sout: VarSet.t):
    CFGProgD.get_block p fname bid = Some b -> (* the block exists *)
    BlockD.is_jump_block b = Some next_bid -> (* the block ends with a jump, and next_bid is the id of the next block *)
    live_in p fname next_bid s -> (* s is the set of live variables at the entry of p/fname/next_bid *)
    CFGProgD.get_block p fname next_bid = Some next_b -> (* next_b is the block with id next_bid *)
    VarSet.Equal sout (apply_inv_phi (next_b.(phi_function) bid) s) ->
    live_out p fname bid sout  (* sout is the set of live variable at the exit of p/fname/bid *)

  (* A block with a conditional jump *)
  | lo_block_w_cond_jump (fname : FuncName.t) (bid next_bid_if_true next_bid_if_false:  BlockID.t) (cond_var: VarID.t) (b next_b_if_true next_b_if_false: BlockD.t) (s1 s2 sout: VarSet.t):
    CFGProgD.get_block p fname bid = Some b -> (* the block exists *)
    BlockD.is_cond_jump_block b = Some (cond_var, next_bid_if_true, next_bid_if_false) -> (* the block ends with a conditional jump, and next_bid_if_true and next_bid_if_false are the identifiers of the next blocks *)
    live_in p fname next_bid_if_true s1 ->  (* s1 is the set of live at the entry of p/fname/next_bid_if_true *)
    live_in p fname next_bid_if_false s2 -> (* s2 is the set of live variables at the entry of p/fname/next_bid_if_false *)
    CFGProgD.get_block p fname next_bid_if_true = Some next_b_if_true -> (* next_b_if_true is the block with id next_bid_if_true *)
    CFGProgD.get_block p fname next_bid_if_false = Some next_b_if_false -> (* next_b_if_false is the block with id next_bid_if_false *)
    VarSet.Equal sout (VarSet.union (apply_inv_phi (next_b_if_true.(phi_function) bid) s1) (apply_inv_phi (next_b_if_false.(phi_function) bid) s2)) ->
    live_out p fname bid sout
  with
    live_in (p : CFGProgD.t) : FuncName.t -> BlockID.t -> VarSet.t -> Prop :=
  | li_block_any (fname : FuncName.t) (bid :  BlockID.t) (b: BlockD.t) (s sout: VarSet.t):
    CFGProgD.get_block p fname bid = Some b -> (* the block exists *)
    live_out p fname bid s -> (* s is the set of live variables at the exit of p/fname/bid *)
    VarSet.Equal sout (prop_live_set_bkw b.(instructions) (add_jump_var_if_applicable b s)) ->
    live_in p fname bid sout.

  (* Defines the live variables set at every program point. It
     basically propagates the live-out set of the corresponding block
     backwards. We could incorporate it in the defintion of live
     in/out above, but this was is simpler for the proofs.  *)
  Inductive live_at_pc (p : CFGProgD.t) : FuncName.t -> BlockID.t -> nat -> VarSet.t -> Prop :=
  | live_at_pc_eob (fname : FuncName.t) (bid :  BlockID.t) (b: BlockD.t) (pc: nat) (s sout: VarSet.t):
    CFGProgD.get_block p fname bid = Some b -> (* the block exists *)
    live_out p fname bid s ->
    pc = (length b.(BlockD.instructions)) ->
    VarSet.Equal sout (add_jump_var_if_applicable b s) ->
    live_at_pc p fname bid pc sout
  | live_at_pc_inb (fname : FuncName.t) (bid :  BlockID.t) (b: BlockD.t) (pc: nat) (s sout: VarSet.t) (i: InstrD.t):  
    CFGProgD.get_block p fname bid = Some b -> (* the block exists *)
    live_at_pc p fname bid (S pc) s ->
    Nat.lt pc (length b.(BlockD.instructions)) ->
    nth_error b.(BlockD.instructions) pc = Some i ->
    VarSet.Equal sout (prop_live_set_bkw_instr i s) ->
    live_at_pc p fname bid pc sout.

  (* another way of defining live_at_pc, mainly used as a bridge to
  showing that live_at_pc for pc=0 is the same as live_in. AT some
  point we should eliminate this definition. *) 
  Inductive live_at_pc' (p : CFGProgD.t) : FuncName.t -> BlockID.t -> nat -> VarSet.t -> Prop :=
  | live_at_pc_1 (fname : FuncName.t) (bid :  BlockID.t) (b: BlockD.t) (pc: nat) (s sout: VarSet.t):
    CFGProgD.get_block p fname bid = Some b -> (* the block exists *)
    live_out p fname bid s ->
    Nat.le pc (length b.(BlockD.instructions)) ->
    VarSet.Equal sout (prop_live_set_bkw_aux ((length b.(BlockD.instructions)) - pc) (rev b.(BlockD.instructions)) (add_jump_var_if_applicable b s)) ->
    live_at_pc' p fname bid pc sout.

  (* helper lemma for the one below *)
  Lemma prop_live_set_bkw_aux_i_breakdown:
    forall (n: nat) (l: list InstrD.t) (s: VarSet.t) (i: InstrD.t),
      nth_error l n = Some i ->
      prop_live_set_bkw_aux (S n) l s = 
        prop_live_set_bkw_instr i (prop_live_set_bkw_aux n l s).
  Proof.
    induction n as [| k IH].
  
    - intros l s i H_nth.
      destruct l as [| h t].
    + simpl in H_nth. discriminate.
    + (* Head element: nth_error is Some h *)
      simpl in H_nth. injection H_nth as H_h_eq_i.
      subst.
      simpl. reflexivity.

  - intros l s i H_nth.
    destruct l as [| h t].
    + simpl in H_nth. discriminate.
    + simpl in H_nth.
      simpl.      
      rewrite <- (IH t (prop_live_set_bkw_instr h s) i H_nth).
      * reflexivity.
  Qed.


  (* Defines how [prop_live_set_bkw_aux] applied to (S n) elements can
  be constructed from applying it to n elements. It is not
  straightforward because the function is iterative. It is mainly used
  to prove equivalence of live_at_pc and live_at_pc'
   *)
  Lemma prop_live_set_bkw_aux_i:
    forall l n s i,
      S n <= length l ->
      nth_error l ((length l) - (S n)) = Some i ->
      prop_live_set_bkw_aux (S n) (rev l) s =
        prop_live_set_bkw_instr i (prop_live_set_bkw_aux n (rev l) s).
  Proof.
    intros l n s i H_bound H_nth_l.
    apply prop_live_set_bkw_aux_i_breakdown.
    rewrite nth_error_rev.
    
    assert(H_S_le_lt: forall x y, S x <= y -> x < y). intros. lia.
    apply H_S_le_lt in H_bound.
    
    rewrite <- Nat.ltb_lt in H_bound.
    rewrite H_bound.
    exact H_nth_l.
  Qed.

  (* Equivalence between [live_at_pc'] and [live_at_pc] *)
  Lemma live_at_pc'_equiv_live_at_pc:
    forall i p fname bid b s,
      CFGProgD.get_block p fname bid = Some b -> (* the block exists *)
      Nat.le i (length b.(instructions)) ->
      live_at_pc' p fname bid ((length b.(instructions)) - i) s -> live_at_pc p fname bid ((length b.(instructions)) - i) s.
  Proof.
    induction i as [|i' IHi'].
    - intros p fname bid b s H_b_exists H_lt_0 H_live_at_pc.
      rewrite Nat.sub_0_r.
      rewrite Nat.sub_0_r in H_live_at_pc.
      
      remember (length (BlockD.instructions b)) as pc eqn:E_pc.
      destruct H_live_at_pc as [fname bid b0 pc s sout H_b0_exists H_live_out H_lr_pc H_sout].
      
      rewrite H_b_exists in H_b0_exists.
      injection H_b0_exists as H_b0_exists.
      subst b0.
      
      rewrite E_pc in H_sout.
      rewrite Nat.sub_diag in H_sout.
      simpl in H_sout. 
      apply (live_at_pc_eob p fname bid b pc s sout H_b_exists H_live_out E_pc H_sout).
      
    - intros p fname bid b s H_b_exists H_lt_0 H_live_at_pc.
      remember (length (BlockD.instructions b) - S i') as pc eqn:E_pc.

      assert (H: (length (BlockD.instructions b) - i') = S pc). lia.
      
      destruct H_live_at_pc as [fname bid b0 pc s sout H_b0_exists H_live_out H_lr_pc H_sout].
      
      rewrite H_b_exists in H_b0_exists.
      injection H_b0_exists as H_b0_exists.
      subst b0.

      assert(H0: Nat.le (S pc) (length (BlockD.instructions b))). lia.
      
      assert(H1: (length (BlockD.instructions b) - pc) = S i'). lia.
      rewrite H1 in H_sout.
      
      assert(H2: (length (BlockD.instructions b) - S i') < length (BlockD.instructions b) ). lia.
      
      apply valid_index_nth_error in H2 as [i H_nth].
      
      pose proof (prop_live_set_bkw_aux_i (BlockD.instructions b) i' (add_jump_var_if_applicable b s) i H_lt_0 H_nth) as H2.
      rewrite H2 in H_sout.
      
      remember (prop_live_set_bkw_aux i' (rev (BlockD.instructions b)) (add_jump_var_if_applicable b s)) as s' eqn:E_s'.
      
      assert(H3: Nat.le (S pc) (length (BlockD.instructions b))). lia.
      
      assert (H4: (length (BlockD.instructions b) - S pc) = i'). lia.
      
      rewrite <- H4 in E_s'.
      
      assert (H5: VarSet.Equal s' (prop_live_set_bkw_aux (length (BlockD.instructions b) - S pc) (rev (BlockD.instructions b)) (add_jump_var_if_applicable b s))). rewrite E_s'. apply varset_equal_refl.
      
      pose proof (live_at_pc_1 p fname bid b (S pc) s s' H_b_exists H_live_out H3 H5) as H6.
       
      rewrite <- H in H6.
      
      assert (H7: Nat.le i' (length (BlockD.instructions b))). lia.
      pose proof (IHi' p fname bid b s' H_b_exists H7 H6) as H8.
      rewrite H in H8.
      
      assert(H9: Nat.lt pc (length (BlockD.instructions b))). lia.
      rewrite <- E_pc in H_nth.
      apply (live_at_pc_inb p fname bid b pc s' sout i H_b_exists H8 H9 H_nth H_sout).
  Qed.


  (* relation of live_in to live_at_pc' at pc=0 *)
  Lemma live_at_pc'_zero_eq_live_in:
    forall p fname bid s,
      live_at_pc' p fname bid 0%nat s <-> live_in p fname bid s.
  Proof.
    intros p fname bid s.
    remember 0%nat as pc eqn:H_pc_0.
    split.
    - intros H_live_at_pc'.
      destruct H_live_at_pc' as [fname bid b pc s sout H_b_exists H_live_out H_lt_pc H_sout].
      subst pc.
      rewrite Nat.sub_0_r in H_sout.
      destruct b.(instructions) as [|i l] eqn:H_instrs.
      + pose proof (@li_block_any p fname bid b s sout H_b_exists H_live_out) as H_live_in.
        rewrite H_instrs in H_live_in.
        simpl in *.
        apply (H_live_in H_sout).
      + pose proof (@li_block_any p fname bid b s sout H_b_exists H_live_out) as H_live_in.
        pose proof (prop_live_set_bkw_is_prop_aux (i :: l) (add_jump_var_if_applicable b s)) as H_prop.
        rewrite H_instrs in H_live_in.
        rewrite H_prop in H_live_in.
        apply (H_live_in H_sout).
    - intro H_live_in.
      destruct H_live_in as [fname bid b s sout H_b_exists H_live_out H_sout].
      pose proof (live_at_pc_1 p fname bid b 0 s sout H_b_exists H_live_out (le_0_n (Datatypes.length b.(instructions)))) as H_live_at_pc.

      rewrite prop_live_set_bkw_is_prop_aux in H_sout.
      rewrite Nat.sub_0_r in H_live_at_pc.
      rewrite H_pc_0.
      apply ( H_live_at_pc H_sout).
  Qed.

  (* live_at_pc' with pc=0 is equal to live_at_pc with pc=0 *)
  Lemma live_at_pc'_0_equiv_live_at_pc_0:
    forall p fname bid b s,
      CFGProgD.get_block p fname bid = Some b -> (* the block exists *)
      live_at_pc' p fname bid 0%nat s -> live_at_pc p fname bid 0%nat s.
  Proof.
    intros p fname bid b s H_b_exists H_live_at.
    assert (H: (length (BlockD.instructions b) - length (BlockD.instructions b)) = 0). lia.
    rewrite <- H in H_live_at.
    pose proof (live_at_pc'_equiv_live_at_pc (length (BlockD.instructions b)) p fname bid b s H_b_exists (Nat.le_refl (length (BlockD.instructions b)) ) H_live_at) as H0.
    rewrite H in H0.
    apply H0.
  Qed.

  (* live_in give us live_at_pc' at pc=0. All the above was just for
  that! The other way around is also correct, but not needed for now
  *)
  Lemma live_at_pc_zero_eq_live_in:
    forall p fname bid b s,
      CFGProgD.get_block p fname bid = Some b -> (* the block exists *)
       live_in p fname bid s -> live_at_pc p fname bid 0%nat s.
  Proof.
    intros p fname bid b s H_b_exists.
    pose proof (live_at_pc'_zero_eq_live_in p fname bid s) as H.
    intros H_live_in.
    rewrite <- H in H_live_in.
    apply (live_at_pc'_0_equiv_live_at_pc_0 p fname bid b s H_b_exists) in H_live_in.
    apply H_live_in.
  Qed.


  (* live_in holds for equal sets *)
  Lemma live_in_varset_eq:
    forall p f bid s1 s2,
      VarSet.Equal s1 s2 ->
      live_in p f bid s1 <->
      live_in p f bid s2.
  Proof.
    intros p f bid s1 s2 H_s1_eq_s2.
    split.
    - intros H_live_in_s1.
      destruct H_live_in_s1 as [fname bid b s sout H_b_exists H_live_out H_sout].
      
      rewrite varset_equal_sym in H_sout.
      pose proof (varset_equal_trans (prop_live_set_bkw (BlockD.instructions b) (add_jump_var_if_applicable b s)) sout s2 H_sout H_s1_eq_s2) as H0.
      rewrite varset_equal_sym in H0.
      apply (@li_block_any p fname bid b s s2 H_b_exists H_live_out H0).
    - intros H_live_in_s1.
      destruct H_live_in_s1 as [fname bid b s sout H_b_exists H_live_out H_sout].

      pose proof (varset_equal_trans s1 sout (prop_live_set_bkw (BlockD.instructions b) (add_jump_var_if_applicable b s)) H_s1_eq_s2 H_sout) as H0.

      apply (@li_block_any p fname bid b s s1 H_b_exists H_live_out H0).
  Qed.



  (* All block have live-variable results in r *)
  Definition snd_res_for_all_blocks (p : CFGProgD.t)  (r: prog_live_info_t) : Prop :=
    forall bid f b,
      CFGProgD.get_block p f bid = Some b -> 
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
  Definition snd_block_out_info (p : CFGProgD.t) (r: prog_live_info_t) (fname: FuncName.t) (b: BlockD.t) : Prop :=
    exists f_info b_in_info b_out_info,
      (r fname) = Some f_info /\ (* The live-variable information of the function exists *)
        f_info b.(bid) = Some (b_in_info,b_out_info) /\ (* The live-variable information of the block exists *)
        match b.(exit_info) with
        | ExitInfoD.Terminate =>
            VarSet.Equal b_out_info  VarSet.empty 
        | ExitInfoD.ReturnBlock rs => 
            VarSet.Equal b_out_info (list_to_set (extract_yul_vars rs))
        | ExitInfoD.Jump next_bid =>
            exists next_b next_b_in_info next_b_out_info,
            CFGProgD.get_block p fname next_bid = Some next_b /\ 
              f_info next_bid = Some (next_b_in_info,next_b_out_info) /\
              VarSet.Equal b_out_info (apply_inv_phi (next_b.(phi_function) b.(bid)) next_b_in_info)
        | ExitInfoD.ConditionalJump cond_var next_bid_if_true next_bid_if_false => 
            exists next_b_if_true next_b_ift_in_info next_b_ift_out_info next_b_if_false next_b_iff_in_info next_b_iff_out_info,
            CFGProgD.get_block p fname next_bid_if_true = Some next_b_if_true /\ 
            CFGProgD.get_block p fname next_bid_if_false = Some next_b_if_false /\ 
              f_info next_bid_if_true = Some (next_b_ift_in_info,next_b_ift_out_info) /\
              f_info next_bid_if_false = Some (next_b_iff_in_info,next_b_iff_out_info) /\
              VarSet.Equal b_out_info (VarSet.union
                                         (apply_inv_phi (phi_function next_b_if_true b.(bid)) next_b_ift_in_info)
                                         (apply_inv_phi (phi_function next_b_if_false b.(bid)) next_b_iff_in_info))
        end.
 
  Definition snd_block_in_info (r: prog_live_info_t) (fname: FuncName.t) (b: BlockD.t) : Prop :=
    exists f_info b_in_info b_out_info,
      (r fname) = Some f_info /\ (* The live-variable information of the function exists *)
        f_info b.(bid) = Some (b_in_info,b_out_info) /\ (* The live-variable information of the block exists *)
        VarSet.Equal b_in_info (prop_live_set_bkw b.(instructions) (add_jump_var_if_applicable b b_out_info)).
  
  Definition snd_block_info (p: CFGProgD.t) (r: prog_live_info_t) (f: FuncName.t) (b: BlockD.t)
    : Prop :=
    snd_block_in_info r f b /\ snd_block_out_info p r f b.

  Definition snd_all_blocks_info (p : CFGProgD.t) (r: prog_live_info_t) : Prop :=
    forall fname bid b,
      CFGProgD.get_block p fname bid = Some b -> (* if the block exists *)
      snd_block_info p r fname b. (* it has sound information *)


  (* When get_block succeeds, it block it return indeed has the expected bid *)
  Lemma bid_b:
    forall p fname bid b,
      CFGProgD.get_block p fname bid = Some b -> b.(BlockD.bid) = bid.
  Proof.
    intros p fname bid b H_exists.
    unfold CFGProgD.get_block in H_exists.
    destruct (CFGProgD.get_func p fname) as [func|]; try discriminate.
    unfold get_block in H_exists.
    destruct (find (fun b : BlockD.t => BlockID.eqb b.(BlockD.bid) bid) func.(blocks)) as [block|] eqn:H_find; try discriminate.
    apply find_some in H_find.
    destruct H_find as [_ H_find].
    rewrite BlockID.eqb_eq in H_find.
    injection H_exists as H_t0_b.
    rewrite H_t0_b in H_find.
    apply H_find.
  Qed.

   
  Lemma exit_info_vs_is_cond_jump:
    forall b cond_var bid_if_true bid_if_false,
      b.(exit_info) = ExitInfoD.ConditionalJump cond_var bid_if_true bid_if_false ->
      BlockD.is_cond_jump_block b = Some (cond_var, bid_if_true, bid_if_false).
  Proof.
    intros b cond_var bid_if_true bid_if_false H.
    unfold BlockD.is_cond_jump_block.
    rewrite H.
    reflexivity.
  Qed.

  Lemma exit_info_vs_is_jump:
    forall b bid,
      b.(exit_info) = ExitInfoD.Jump bid ->
      BlockD.is_jump_block b = Some bid.
  Proof.
    intros b target H.
    unfold BlockD.is_jump_block.
    rewrite H.
    reflexivity.
  Qed.

  Lemma exit_info_vs_is_return:
    forall b rs,
      b.(exit_info) = ExitInfoD.ReturnBlock rs ->
      BlockD.is_return_block b = Some rs.
  Proof.
    intros b rs H.
    unfold BlockD.is_return_block.
    rewrite H.
    reflexivity.
  Qed.

  Lemma exit_info_vs_is_terminated:
    forall b,
      b.(exit_info) = ExitInfoD.Terminate ->
      BlockD.is_terminated_block b = true.
  Proof.
    intros b H.
    unfold BlockD.is_terminated_block.
    rewrite H.
    reflexivity.
  Qed.
  

  CoFixpoint build_live_in (p : CFGProgD.t) (fname: FuncName.t) (bid: BlockID.t) (b: BlockD.t)
    (r: prog_live_info_t) (f_info: func_live_info_t) (b_in_info b_out_info: VarSet.t)
    (H_snd_info: snd_all_blocks_info p r) (H_b_exists: CFGProgD.get_block p fname bid = Some b)
    (H_f_info: (r fname) = Some f_info) (H_b_info: f_info bid = Some (b_in_info,b_out_info)) : live_in p fname bid b_in_info
  with build_live_out (p : CFGProgD.t) (fname: FuncName.t) (bid: BlockID.t) (b: BlockD.t)
         (r: prog_live_info_t) (f_info: func_live_info_t) (b_in_info b_out_info: VarSet.t)
                           (H_snd_info: snd_all_blocks_info p r) (H_b_exists: CFGProgD.get_block p fname bid = Some b)
                           (H_f_info: (r fname) = Some f_info) (H_b_info: f_info bid = Some (b_in_info,b_out_info)) : live_out p fname bid b_out_info.
  Proof.
    (* the case of live_in p fname bid b_in_info *)
    - unfold snd_all_blocks_info in H_snd_info.
      pose proof (H_snd_info fname bid b H_b_exists) as H_snd_b_info.
      unfold snd_block_info in H_snd_b_info.
      destruct H_snd_b_info as [H_snd_b_in_info H_snd_b_out_info].
      unfold snd_block_in_info in H_snd_b_in_info.
      destruct H_snd_b_in_info as [f_info' [b_in_info' [b_out_info' [H_r_f [H_f_info' H_b_in_info']]]]].
      rewrite (bid_b p fname bid b H_b_exists) in H_f_info'.
      
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

      apply (@li_block_any p fname bid b b_out_info' b_in_info' H_b_exists).

      apply (build_live_out p fname bid b r f_info' b_in_info' b_out_info' H_snd_info H_b_exists H_r_f  H_f_info').
      
      apply H_b_in_info'.            
        
    (* the case of live_out p fname bid b_in_info *)
    - pose proof (H_snd_info fname bid b H_b_exists) as H_snd_b_info.
      unfold snd_block_info in H_snd_b_info.
      destruct H_snd_b_info as [H_snd_b_in_info H_snd_b_out_info].
      unfold snd_block_out_info in H_snd_b_out_info.
      destruct H_snd_b_out_info as [f_info' [b_in_info' [b_out_info' [H_r_f [H_f_info' H_b_out_info']]]]].
      rewrite (bid_b p fname bid b H_b_exists) in H_f_info'.
  
      assert (H_f_info_info': f_info = f_info').
      (*{*)
      rewrite H_f_info in H_r_f. injection H_r_f as H_r_f. apply H_r_f.
      (*{*)

      rewrite (bid_b p fname bid b H_b_exists) in H_b_out_info'.

      assert (H_b_out_info_info': b_out_info = b_out_info').
      (*{*)
      rewrite <- H_f_info_info' in H_f_info'. rewrite H_b_info in H_f_info'. injection H_f_info' as _ H_b_out_info_info'. rewrite H_b_out_info_info'. reflexivity.
      (*{*)
             
      destruct b.(BlockD.exit_info) as [cond_var target_if_true target_if_false | target | return_values | ] eqn:E_exit_info.

      (* conditional jump *)
      + destruct H_b_out_info' as [next_b_if_true [ next_b_ift_in_info [next_b_ift_out_info [next_b_if_false [ next_b_iff_in_info [next_b_iff_out_info [H_b_next_ift_exists [H_b_next_iff_exists [H_f_ift_info' [H_f_iff_info' H_b_out_info']]]]]]]]]].

      rewrite H_b_out_info_info'.
      
      apply  (@lo_block_w_cond_jump p fname bid target_if_true target_if_false cond_var b next_b_if_true next_b_if_false next_b_ift_in_info next_b_iff_in_info b_out_info' H_b_exists (exit_info_vs_is_cond_jump b cond_var target_if_true target_if_false E_exit_info) (build_live_in p fname target_if_true next_b_if_true r f_info' next_b_ift_in_info next_b_ift_out_info H_snd_info H_b_next_ift_exists H_r_f H_f_ift_info') (build_live_in p fname target_if_false next_b_if_false r f_info' next_b_iff_in_info next_b_iff_out_info H_snd_info H_b_next_iff_exists H_r_f H_f_iff_info') H_b_next_ift_exists H_b_next_iff_exists H_b_out_info').

      (* jump *)
      + destruct H_b_out_info' as [next_b [next_b_in_info [next_b_out_info [H_b_next_exists [H_f_next_b_info' H_next_b_out_info']]]]].

      rewrite H_b_out_info_info'.

      apply (@lo_block_w_jump p fname bid target b next_b next_b_in_info b_out_info' H_b_exists (exit_info_vs_is_jump b target E_exit_info) (build_live_in p fname target next_b r f_info' next_b_in_info next_b_out_info H_snd_info H_b_next_exists H_r_f H_f_next_b_info') H_b_next_exists H_next_b_out_info').

      (* return *)
      + rewrite H_b_out_info_info'.
        apply (@lo_block_w_ret p fname bid b return_values b_out_info' H_b_exists (exit_info_vs_is_return b return_values E_exit_info ) H_b_out_info').

      (* teminate *)
      + rewrite H_b_out_info_info'.
        apply (@lo_block_w_ter p fname bid b b_out_info' H_b_exists (exit_info_vs_is_terminated b E_exit_info) H_b_out_info' ).
  Defined.

  Lemma snd_all_blocks_info_to_bid_info:
    forall (p : CFGProgD.t) (r: prog_live_info_t),
      snd_all_blocks_info p r ->  
      forall fname bid b,
        CFGProgD.get_block p fname bid = Some b ->
        exists f_info b_in_info b_out_info,
          (r fname) = Some f_info /\
            f_info bid = Some (b_in_info,b_out_info).
  Proof.
    intros p r H_snd_info fname bid b H_b_exists.
    pose proof (H_snd_info fname bid b H_b_exists) as H_b_info_snd.
    unfold snd_block_info in H_b_info_snd.
    destruct H_b_info_snd as [H_b_in_info_snd _].
    unfold snd_block_in_info in H_b_in_info_snd.
    rewrite (bid_b p fname bid b H_b_exists) in H_b_in_info_snd.
    destruct H_b_in_info_snd as [f_info [b_in_info [b_out_info [H_r_f [H_f_info _]]]]].
    exists f_info, b_in_info, b_out_info.
    split; assumption.
  Qed.
  
  Lemma snd_info:
    forall (p : CFGProgD.t) (r: prog_live_info_t),
      snd_all_blocks_info p r ->  
      forall fname bid b,
        CFGProgD.get_block p fname bid = Some b ->
        exists f_info b_in_info b_out_info,
          (r fname) = Some f_info /\
            f_info bid = Some (b_in_info,b_out_info) /\
            live_in p fname bid b_in_info /\
            live_out p fname bid b_out_info.
  Proof.
    intros p r H_snd_info fname bid b H_b_exists.
    pose proof (H_snd_info fname bid b H_b_exists) as H_b_info_snd.
    unfold snd_block_info in  H_b_info_snd.
    destruct H_b_info_snd as [H_b_in_info_snd H_b_out_info_snd].
    pose proof (snd_all_blocks_info_to_bid_info p r H_snd_info fname bid b H_b_exists) as H_snd_all_blocks_info_to_bid_info.
    destruct H_snd_all_blocks_info_to_bid_info as [f_info [b_in_info [b_out_info [H_r_f H_f_info]]]].
    exists f_info, b_in_info, b_out_info.
    repeat split.
    - assumption.
    - assumption.
    - apply (build_live_in p fname bid b r f_info b_in_info b_out_info H_snd_info H_b_exists H_r_f H_f_info).
    - apply (build_live_out p fname bid b r f_info b_in_info b_out_info H_snd_info H_b_exists H_r_f H_f_info).
  Qed.
    
  Lemma check_live_in_snd:
    forall r fname b,
      check_live_in r fname b = true -> snd_block_in_info r fname b.
  Proof.
    intros r fname b H_check_live_in.
    unfold check_live_in in H_check_live_in.
    destruct (r fname) as [f_info|] eqn:E_r_f; try discriminate.
    destruct (f_info (BlockD.bid b)) as [b_info|] eqn:E_f_info_b; try discriminate.
    destruct b_info as [b_in_info b_out_info].
    unfold snd_block_in_info.
    exists f_info, b_in_info, b_out_info.
    split; try assumption.
    split; try assumption.
    rewrite <- VarSet.equal_spec.
    apply H_check_live_in.
  Qed.

  Lemma check_live_in_complete:
    forall r fname b,
      snd_block_in_info r fname b -> check_live_in r fname b = true.
  Proof.
    intros r fname b H_snd.
    unfold snd_block_in_info in H_snd.
    destruct H_snd as [f_info [b_in_info [b_out_info [H_r_f [H_f_info H_eq]]]]].
    unfold check_live_in.
    destruct (r fname) as [f_info'|]; try discriminate.
    injection H_r_f as H_f_info_info'.
    rewrite H_f_info_info'.
    rewrite H_f_info.
    rewrite VarSet.equal_spec.
    apply H_eq.
  Qed.

  Lemma check_live_in_correct:
    forall r fname b,
      snd_block_in_info r fname b <-> check_live_in r fname b = true.
  Proof.
    intros r fname b.
    split.
    + apply check_live_in_complete.
    + apply check_live_in_snd.
  Qed.


  Lemma check_live_out_snd:
    forall p r fname b,
      check_live_out p r fname b = true -> snd_block_out_info p r fname b.
  Proof.
    intros p r fname b H_check_live_out.
    unfold check_live_out in H_check_live_out.
    destruct (r fname) as [f_info|] eqn:E_r_f; try discriminate.
    destruct (f_info (BlockD.bid b)) as [b_info|] eqn:E_f_info_b; try discriminate.
    destruct b_info as [b_in_info b_out_info].
    unfold snd_block_out_info.
    exists f_info. exists b_in_info. exists b_out_info.
    split; try assumption.
    split; try assumption.
    destruct (BlockD.exit_info b) as [cond_var bid_if_true bid_if_false|next_bid|rs|] eqn:E_b_exit_info.

    + destruct (CFGProgD.get_block p fname bid_if_true) as [next_b_if_true|]; try discriminate.
      destruct (CFGProgD.get_block p fname bid_if_false) as [next_b_if_false|]; try discriminate.
      destruct (f_info bid_if_true) as [bid_if_true_info|]; try discriminate.
      destruct bid_if_true_info as [next_b_ift_in_info next_b_ift_out_info].
      destruct (f_info bid_if_false) as [target_if_false_info|]; try discriminate.
      destruct target_if_false_info as [next_b_iff_in_info next_b_iff_out_info].

      exists next_b_if_true, next_b_ift_in_info, next_b_ift_out_info, next_b_if_false, next_b_iff_in_info, next_b_iff_out_info.
      split; try reflexivity.
      split; try reflexivity.
      split; try reflexivity.
      split; try reflexivity.
      rewrite <- VarSet.equal_spec.
      apply H_check_live_out.

    + destruct (CFGProgD.get_block p fname next_bid) as [next_b|]; try discriminate.
      destruct (f_info next_bid) as [next_bid_info|]; try discriminate.
      destruct next_bid_info as [next_b_in_info next_b_out_info].
      exists next_b, next_b_in_info, next_b_out_info.
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
    forall p r fname b,
      snd_block_out_info p r fname b -> check_live_out p r fname b = true.
  Proof.
    intros p r f b H_snd.
    unfold snd_block_out_info in H_snd.
    destruct H_snd as [f_info [b_in_info [b_out_info [H_r_f [H_f_info H_eq]]]]].
    unfold check_live_out.
    rewrite H_r_f.
    rewrite H_f_info.

    destruct b.(exit_info) as [cond_var bid_if_true bid_if_false|next_bid|rs|] eqn:E_b_exit_info.

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
    forall p r fname b,
      snd_block_out_info p r fname b <-> check_live_out p r fname b = true.
  Proof.
    intros p r fname b.
    split.
    + apply check_live_out_complete.
    + apply check_live_out_snd.
  Qed.

  Lemma check_live_snd:
    forall p r fname b,
      check_live p r fname b = true -> snd_block_info p r fname b.
  Proof.
    intros p r fname b H_check_live.
    unfold check_live in H_check_live.
    destruct (check_live_in r fname b) eqn:E_check_live; try discriminate.
    unfold snd_block_info.
    split.
    + apply (check_live_in_snd r fname b E_check_live).
    + apply (check_live_out_snd p r fname b H_check_live).
  Qed.

  Lemma check_live_complete:
    forall p r fname b,
      snd_block_info p r fname b -> check_live p r fname b = true.
  Proof.
    intros p r fname b H_snd.
    unfold snd_block_info in H_snd.
    destruct H_snd as [H_snd_in H_snd_out].
    unfold check_live.
    rewrite (check_live_in_complete r fname b H_snd_in).
    rewrite (check_live_out_complete p r fname b H_snd_out).
    reflexivity.
  Qed.

  Lemma check_live_correct:
    forall p r fname b,
      snd_block_info p r fname b <-> check_live p r fname b = true.
  Proof.
    intros p r fname b.
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

  (* If a [P e] holds for all [e] in a list, then it holds fro all elements in the tail *)
  Lemma in_cons_if_prop:
    forall {A: Type} (b : A) (bs: list A) (P: A->Prop),
      (forall e, List.In e (b::bs) -> P e) ->
      (forall e, List.In e bs -> P e).
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
        In f fs -> forall b, In b f.(blocks) -> snd_block_info p r f.(name) b.
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
        destruct (check_blocks f.(blocks) f.(name) p r) eqn:E_check_f; try discriminate.
        apply (check_blocks_snd f.(blocks) f.(name) p r E_check_f b H_in_b_blocks_f0).
      + simpl in H_check_functions.
        destruct (check_blocks f.(blocks) f.(name)); try discriminate.
        apply (IHfs' p r H_check_functions f0 H_in_f0_fs' b H_in_b_blocks_f0).
  Qed.

  
  Lemma check_functions_complete:
    forall fs p r,
      (forall f, 
          In f fs -> forall b, In b f.(blocks) -> snd_block_info p r f.(name) b) ->
      check_functions fs p r = true.
  Proof.
    induction fs as [|f fs' IHfs'].
    - simpl.
      intros p r H_snd.
      reflexivity.
    - intros p r H_snd.
      pose proof (H_snd f) as  H_snd_f.
      simpl.
      destruct (check_blocks f.(blocks) f.(name) p r) eqn:E_check_f_blocks.
      + apply IHfs'.
        intros f0 H_in_f0_fs' b.
        apply (H_snd f0 (in_cons f f0 fs' H_in_f0_fs') b).
      + rewrite (check_blocks_complete f.(blocks) f.(name) p r (H_snd_f (in_eq f fs'))) in E_check_f_blocks.
        discriminate E_check_f_blocks.
  Qed.
  
  Lemma check_program_snd:
    forall p r,
    check_program p r = true ->
    forall f,
        In f p.(functions) -> forall b, In b f.(blocks) -> snd_block_info p r f.(name) b.
  Proof.
    intros p r H_check_sc.
    intros f H_in_f_pfs b H_b_in_bsf.
    unfold check_program in H_check_sc.
    apply (check_functions_snd p.(functions) p r H_check_sc f H_in_f_pfs b H_b_in_bsf).
  Qed.
    

  Lemma check_program_complete:
    forall p r,
      (forall f,
          In f p.(functions) -> forall b, In b f.(blocks) -> snd_block_info p r f.(name) b) ->
      check_program p r = true.
  Proof.
    intros p r H_snd.
    unfold check_program.
    apply (check_functions_complete p.(functions) p r H_snd).
  Qed.

  Lemma check_program_correct:
    forall p r,
      (forall f,
          In f p.(functions) ->
          forall b, In b f.(blocks) ->
                    snd_block_info p r f.(name) b) <-> check_program p r = true.
    Proof.
      intros p r.
      split.
      - apply check_program_complete.
      - apply check_program_snd.
    Qed.

  (* This is the main theorem about the livness checking procedure,
  without refering to live_in and live_ot. Using snd_info, we can
  replace snd_all_blocks_info by one that is based on live_in and
  live_out --- should be done later *)
  Lemma check_prog_w_valid_smart_contract_correct:
    forall p r,
      CFGProgD.valid_program p ->
      snd_all_blocks_info p r <-> check_program p r = true.
  Proof.
    intros p r H_valid_p.
    rewrite <- check_program_correct.
    unfold snd_all_blocks_info.
    split.
    - intro H_get_block_imp_snd.
      pose proof (CFGProgD.valid_p_vs_get_block p H_valid_p) as H_valid_p_vs_get_block.

      intros f H_f_in_pfs b H_b_in_fbs.
      apply (H_get_block_imp_snd f.(name) b.(bid) b).
      rewrite H_valid_p_vs_get_block.
      exists f.
      
      repeat split.
      + apply H_f_in_pfs.
      + apply H_b_in_fbs.
      + rewrite FuncName.eqb_eq. reflexivity.
      + rewrite BlockID.eqb_eq. reflexivity.          

    - intros H_snd.
      intros fname bid b H_get_block.

      rewrite (CFGProgD.valid_p_vs_get_block p H_valid_p fname bid b) in H_get_block.

      destruct H_get_block as [f [H_f_in_pfs [H_b_in_fbs [H_f_name_eqb_fname H_b_bid_eqb_bid]]]].
      rewrite FuncName.eqb_eq in H_f_name_eqb_fname.
      subst fname.
      
      apply (H_snd f H_f_in_pfs b H_b_in_fbs).
  Qed.



  (* In what follows we develop the semantic meaning of liveness,
  i.e., what live_in and live_out sets tell us about executions. This
  is required to show that the analysis that is based on solving the
  corresoinding equation is sound wrt. *)
  

  (*

  This defintion states that a call stack can be split around a frame at
  position i, when counting from the end, i.e., the 0th position is
  the end of the list.

  [f3,f2,f1,f0] <- l
  [f3,f2,f1]+f0::[] i = 0
  [f3,f2]+f1::[f0] i = 1
  [f3]+f2::[f1,f0] i = 2
  []+f3::[f2,f1,f0] i = 3              
 *)
  Definition split_at_i {A : Type} (i: nat) (l hl tl: list A) (a: A) :=
      Nat.lt i (length l) /\ l = hl++(a::tl) /\ length tl = i.

  (* helper lemma, if n=m+n then m is zero *)
  Lemma n_eq_n_plus_m:
    forall n m, n = m+n -> m=0.
  Proof.
    intros m n H.
    lia.
  Qed.

  (* When splitting around i=0, the tail is empty *)
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

  (* When splitting around the first element of the list, the head is empty *)
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
          

  (* Defines what are the variables that will be immediately accessed
  in the next execution step, assuming it will be on block b and pc
  counter pc *)
  Definition accessed_vars (b: BlockD.t) (pc: nat) (s: VarSet.t) :=
    ( pc = (length b.(instructions)) /\
        match b.(exit_info) with
        | ExitInfoD.ConditionalJump cv _ _ => (VarSet.Equal s (VarSet.add cv VarSet.empty))
        | ExitInfoD.ReturnBlock rvs => (VarSet.Equal s (list_to_set (extract_yul_vars rvs)))
        | _ => VarSet.Equal s VarSet.empty
        end
    )
    \/
    (  pc < (length b.(instructions)) /\
         exists i,
           nth_error b.(instructions) pc = Some i /\
             (VarSet.Equal s (list_to_set (extract_yul_vars i.(input)))) 
    ).

  (* The following lemma states when the top stack frames of two states
  are equivalent wrt to the accessed variables*)
  Definition equiv_vars_in_top_frame (p: CFGProgD.t) (st1 st2: StateD.t) :=
    match st1.(call_stack), st2.(call_stack) with
    | nil,nil => True
    | sf1::_,sf2::_ =>
        sf1.(fname) = sf2.(fname) /\
        sf1.(curr_bid) = sf2.(curr_bid) /\
        sf1.(pc) = sf2.(pc) /\
        forall v s b,
          CFGProgD.get_block p sf1.(fname) sf1.(curr_bid) = Some b ->
          accessed_vars b sf1.(StackFrameD.pc) s ->
          VarSet.In v s ->
          D.eqb (LocalsD.get sf1.(locals) v) (LocalsD.get sf2.(locals) v) = true
    | _,_ => False
    end.

  (* [equiv_vars_in_top_frame] is reflexive *)
  Lemma equiv_vars_in_top_frame_refl:
    forall b st,
      equiv_vars_in_top_frame b st st.
  Proof.
    intros b st.
    unfold equiv_vars_in_top_frame.
    destruct (StateD.call_stack st) as [|sf rsf].
    - apply I.
    - repeat split.
      intros.
      rewrite DialectFactsD.eqb_eq.
      reflexivity.
  Qed.

  Definition eq_locals (locals1 locals2: LocalsD.t) :=
    forall v', (LocalsD.get locals1 v') = (LocalsD.get locals2 v').

  Definition equiv_locals (locals1 locals2: LocalsD.t) :=
    forall v', D.eqb (LocalsD.get locals1 v') (LocalsD.get locals2 v') = true.
  
  Definition equiv_locals_up_to_v (locals1 locals2: LocalsD.t) (v: VarID.t) :=
    forall v', v'<>v ->
               D.eqb (LocalsD.get locals1 v') (LocalsD.get locals2 v') = true.

  (* Defines when two stack frame are equivalent up to the value of variable [v]*)
  Definition equiv_stack_frames_up_to_v (fname: FuncName.t) (bid: BlockID.t) (pc: nat) (v: VarID.t) (sf1 sf2: StackFrameD.t) :=
    sf1.(StackFrameD.fname) = fname /\
      sf1.(StackFrameD.curr_bid) = bid /\
      sf1.(StackFrameD.pc) = pc /\ 
      sf2.(StackFrameD.fname) = fname /\
      sf2.(StackFrameD.curr_bid) = bid /\
      sf2.(StackFrameD.pc) = pc /\
      equiv_locals_up_to_v  sf1.(locals)  sf2.(locals) v.

  (* Defines when two states are equivalent up to the value of vaiable [v] in the i-th stack frame *)
  Definition equiv_states_up_to_i_v (p: CFGProgD.t) (i: nat) (fname: FuncName.t) (bid: BlockID.t) (pc: nat) (v: VarID.t) (st1 st2: StateD.t) :=
    Nat.lt i (length st1.(call_stack)) /\ (* the i frame exists *)
      (length st1.(call_stack)) = (length st2.(call_stack)) /\ (* call stacks have the same length *)
      st1.(StateD.status) = st2.(StateD.status) /\ (* same status *)
      st1.(StateD.dialect_state) = st2.(StateD.dialect_state) /\ (* same dialect states *)
      exists hl tl sf1 sf2, (* i-th frames are equivalent and the rest of frame are identical *)
        split_at_i i st1.(call_stack) hl tl sf1 /\
          split_at_i i st2.(call_stack) hl tl sf2 /\
          equiv_stack_frames_up_to_v fname bid pc v sf1 sf2.

  (* [VarSet.In x s] is decdiable *)
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

  (* If existsb does not find an element (of type VarID.t) then [List.In x l] is false *)
  Lemma varlist_in_dec_aux:
    forall l x,
      existsb (fun y => VarID.eqb x y) l = false ->
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
      + symmetry in H_a_eq_x.
        rewrite <- VarID.eqb_eq in H_a_eq_x.
        rewrite H_a_eq_x in H_neq_x_a.
        discriminate H_neq_x_a.
      + pose proof (IHl' x H_existsb_l') as IHl'_inst.
        contradiction.
  Qed.

  (* [List.In x l] is decidable *)
  Lemma varlist_in_dec:
    forall (l: list VarID.t) (x: VarID.t),
      List.In x l \/ ~ List.In x l.
  Proof.
    intros l x.
    destruct (existsb (fun y => VarID.eqb x y) l) eqn:E_exists.
    - rewrite existsb_exists in E_exists.
      destruct E_exists as [x0 [H_in_x0_l H_x0_eqb_x]].
      rewrite VarID.eqb_eq in H_x0_eqb_x.
      left.
      rewrite H_x0_eqb_x.
      apply H_in_x0_l.
    - right.
      apply (varlist_in_dec_aux l x E_exists).
  Qed.

  (* If [a] is not in [b::l], then it is not in [l] *)  
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

  (* as the one above but the with a forall over In *)
  Lemma not_In_cons_forall {A: Type}:
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

  (* If [a] is not in [b::l], then [a<>b] *)  
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

  (* This lemma is used intensively. It states that if two frames
  states are equivalent up to variable v, then evaluating a list of
  expressions that does not contain v result in the same values in bot
  states -- it is based on that [D.eqb a b = true <-> a = b *)
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
        pose proof (H_eq_sf1_sf2 var H_var_neq_v) as H_eqb_1_elt.
        rewrite DialectFactsD.eqb_eq in H_eqb_1_elt.
        rewrite H_eqb_1_elt.
        reflexivity.
      + pose proof ( IHl' fname bid pc v sf1 sf2 H_eq_sf1_sf2 (not_In_cons l' (inl v) (inr val) H_not_in)) as IH_l'.
        rewrite IH_l'.
        reflexivity.
  Qed.
  

    (* If [get_instr] succeeds, then the [pc] is smaller that the length of the list of instruction *)
  Lemma get_instruction_succ:
    forall p fname bid b pc instr,
      CFGProgD.get_block p fname bid = Some b ->
      CFGProgD.get_instr p fname bid pc = Some instr ->
      Nat.lt pc (length b.(instructions)).
  Proof.
    intros p fname bid b pc instr H_b_exists H_get_instr.
    unfold CFGProgD.get_instr in H_get_instr.
    rewrite H_b_exists in H_get_instr.
    pose proof (nth_error_Some b.(instructions) pc) as H_nth_some.
    
    assert (H_nth_not_none: nth_error b.(instructions) pc <> None).
    (*{*)
      intros H_contra.
      rewrite H_contra in H_get_instr.
      discriminate H_get_instr.
    (*}.*)
   
    rewrite H_nth_some in H_nth_not_none.
    exact H_nth_not_none.
  Qed.
  
  (* If [get_instr] succeeds, then the [pc] is smaller that the length of the list of instruction *)
  Lemma get_next_instruction_succ:
    forall st p instruction sf rsf b,
      st.(StateD.call_stack) = sf::rsf ->
      CFGProgD.get_block p sf.(fname) sf.(curr_bid) = Some b ->
      SmallStepD.get_next_instr st p = Some instruction ->
      Nat.lt sf.(pc) (length b.(instructions)).
  Proof.
    intros st p instruction sf rsf b H_call_stack H_block_exists H_get_next.
    unfold SmallStepD.get_next_instr in H_get_next.
    rewrite H_call_stack in H_get_next.
    apply (get_instruction_succ p sf.(fname) sf.(curr_bid) b sf.(pc) instruction H_block_exists H_get_next).
  Qed.

  (* Equivalent states have equal status *)
  Lemma equiv_states_eq_status:
    forall p i fname bid pc v st1 st2,
      equiv_states_up_to_i_v p i fname bid pc v st1 st2 ->
      st1.(status) = st2.(status).
  Proof.
    intros p i fname bid pc v st1 st2 H_equiv_st1_st2.
    apply H_equiv_st1_st2.
  Qed.

  (* Equivalent states have equal dialect *)
  Lemma equiv_states_eq_dialect:
    forall p i fname bid pc v st1 st2,
      equiv_states_up_to_i_v p i fname bid pc v st1 st2 ->
      st1.(dialect_state) = st2.(dialect_state).
  Proof.
    intros p i fname bid pc v st1 st2 H_equiv_st1_st2.
    apply H_equiv_st1_st2.
  Qed.

  (* Equivalent states have non-emtpty call stacks *)
  Lemma equiv_states_non_nil_call_stack:
    forall p i fname bid pc v st1 st2,
      equiv_states_up_to_i_v p i fname bid pc v st1 st2 ->
      st1.(call_stack) <> [] /\ st2.(call_stack) <> [].
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

  (* equivalent states have equivalent frames at the top of call stacks *)
  Lemma equiv_state_equiv_frames_at_top:
    forall p fname bid b pc i v s st1 st2,
      CFGProgD.get_block p fname bid = Some b  ->
      live_at_pc p fname bid pc s ->
      ~ VarSet.In v s ->
      equiv_states_up_to_i_v p i fname bid pc v st1 st2 ->
      equiv_vars_in_top_frame p st1 st2.
  Proof.
    intros p fname bid b pc i v s st1 st2 H_exists_b H_live_at_pc H_not_In_v_s H_eq_st1_st2.

    unfold equiv_states_up_to_i_v in H_eq_st1_st2.
    destruct H_eq_st1_st2 as [H_lt_i [H_len_st1_st2 [_ [_ [ hl [tl [sf1 [sf2 [H_split_i_st1 [H_split_i_st2 H_equiv_frame_up_to_v_sf1_sf2]]]]]]]]]].

    (* We consider two cases: when the i-th frame is the top of the
    call stack and when it is deeper. The second is trivial since they
    are identical *) 
    destruct hl as [|sftop] eqn:E_hl.

    (* the i-th frame is the top of the call stack *)
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
      + intros v0 s0 b_top H_b_top_exists H_acc H_v0_not_In_s0.
        rewrite H_exists_b in H_b_top_exists. injection H_b_top_exists as H_b_top_exists. subst b_top.
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
                      pose proof (not_In_preserves_eq sout (VarSet.add cv s) v H2 H_not_In_v_s) as H_not_In_v_add_cv_s.
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
             pose proof (not_In_preserves_eq sout (VarSet.union (VarSet.diff s (list_to_set (InstrD.output instr))) (list_to_set (extract_yul_vars (InstrD.input instr)))) v H2 H_not_In_v_s).
             rewrite VarSet.union_spec in H.
             apply Decidable.not_or in H.
             destruct H.
             pose proof (In_preserves_eq s0 (list_to_set (extract_yul_vars (InstrD.input instr))) v0 H_s0 H_v0_not_In_s0).
             pose proof (not_In_neq v0 v (list_to_set (extract_yul_vars (InstrD.input instr))) H3 H1).
             apply (H_eq_assgin_up_to_v v0 H4).

    (* the i-th frame is not at the top of the call stack *)
    - unfold split_at_i in H_split_i_st1.
      destruct H_split_i_st1 as [_ [H_split_i_st1 _]].
      simpl in H_split_i_st1.
      unfold split_at_i in H_split_i_st2.
      destruct H_split_i_st2 as [_ [H_split_i_st2 _]].
      simpl in H_split_i_st2.

      unfold equiv_vars_in_top_frame.
      rewrite H_split_i_st1.
      rewrite H_split_i_st2.
      repeat split.
      intros.
      rewrite DialectFactsD.eqb_eq.
      reflexivity.
  Qed.

  (* When [get_next_instr] is applied to equivalent states we get the same instruction *)
  Lemma get_next_instr_eq_states:
    forall p i fname bid pc v st1 st2,
      equiv_states_up_to_i_v p i fname bid pc v st1 st2 ->
      SmallStepD.get_next_instr st1 p = SmallStepD.get_next_instr st2 p. 
  Proof.
    intros p i fname bid pc v st1 st2 H_eq_st1_st2.
    unfold SmallStepD.get_next_instr.
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

  (* [set_status] does not change the call stack *)
  Lemma set_status_preserves_call_stack:
    forall st status,
      st.(call_stack) = (StateD.set_status st status).(call_stack).
  Proof.
    destruct st.
    reflexivity.
  Qed.

  (* [set_status] does not change the dialect state *)
  Lemma set_status_preserves_dialect_state:
    forall st status,
      st.(dialect_state) = (StateD.set_status st status).(dialect_state).
  Proof.
    destruct st.
    reflexivity.
  Qed.

  (* If a variable is in the live sets, then it is not in the accessed set *)
  Lemma accessed_var_instr_neq_v:
    forall p fname bid b pc s0 v0 s v,
      CFGProgD.get_block p fname bid = Some b ->
      live_at_pc p fname bid pc s ->
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
        pose proof (not_In_preserves_eq sout (VarSet.union (VarSet.diff s (list_to_set instr.(output))) (list_to_set (extract_yul_vars instr.(input)))) v H_sout H_not_In_v_s) as H_not_In_v_union.
        rewrite VarSet.union_spec in H_not_In_v_union.
        apply Decidable.not_or in H_not_In_v_union.
        destruct H_not_In_v_union as [_ H_not_in_args].
        pose proof (In_preserves_eq s0 (list_to_set (extract_yul_vars instr.(input))) v0 H_s0 H_In_v0_s0 ) as H_in_v0_args.
        pose proof (not_In_neq v0 v (list_to_set (extract_yul_vars instr.(input))) H_in_v0_args H_not_in_args) as H_neq_v0_v.
        intro H_contra.
        contradiction.
  Qed.

  (* Set all succeeds when input lists have the same length *)
  Lemma set_all_succ:
    forall l vs locals,
      length l = length vs ->
      exists new_locals,        
        LocalsD.set_all locals l vs = Some new_locals.
  Proof.
    induction l as [|a l'].
    - intros vs locals H_len.
      destruct vs; try discriminate.
      exists locals.
      simpl.
      reflexivity.
    - intros vs locals H_len.
      destruct vs as [|v vs']; try discriminate.
      simpl in H_len.
      simpl.
      apply (IHl' vs' (LocalsD.set locals a v) (eq_add_S (length l') (length vs') H_len)).
  Qed.

  (* If variables maps are equivalent up to v, then setting any
  variable we get equivalent maps up to v *)
  Lemma set_preserves_equiv_up_to_v:
    forall locals1 locals2 v a val,
      equiv_locals_up_to_v locals1 locals2 v ->
      equiv_locals_up_to_v (LocalsD.set locals1 a val) (LocalsD.set locals2 a val) v.
  Proof.
    unfold equiv_locals_up_to_v.
    intros locals1 locals2 v a val H.
    intros v' H_neq_v'_v.
    unfold LocalsD.set.
    unfold LocalsD.get.
    destruct (VarID.eqb v' a).
    - rewrite DialectFactsD.eqb_eq.
      reflexivity.
    - apply (H v' H_neq_v'_v).
  Qed.

  (* If variables maps are equivalent up to v, then setting several
  variables we get equivalent maps up to v *)
  Lemma set_all_preserves_eq_up_to:
    forall l locals1 locals2 v vs locals1' locals2',
      ~ List.In v l ->
      equiv_locals_up_to_v locals1 locals2 v ->
      LocalsD.set_all locals1 l vs = Some locals1' ->
      LocalsD.set_all locals2 l vs = Some locals2' ->
      equiv_locals_up_to_v locals1' locals2' v.
  Proof.
    unfold equiv_locals_up_to_v.
    induction l as [| a l'].

    - simpl.
      intros locals1 locals2 v vs locals1' locals2' H_In_v_l H_equiv H_set_all_1 H_set_all_2.
      destruct vs; try discriminate.
      injection H_set_all_1 as H_set_all_1.
      injection H_set_all_2 as H_set_all_2.
      rewrite <- H_set_all_1.
      rewrite <- H_set_all_2.
      apply H_equiv.

    - intros locals1 locals2 v vs locals1' locals2' H_In_v_l H_equiv H_set_all_1 H_set_all_2.
 
      destruct vs as [| v' vs']; try discriminate.
      simpl in H_set_all_1.
      simpl in H_set_all_2.

      simpl in H_In_v_l.
      apply Decidable.not_or in H_In_v_l.
      destruct H_In_v_l as [H_v_neq_a H_In_v_l'].
      
      pose proof (set_preserves_equiv_up_to_v locals1 locals2 v a v' H_equiv) as H_equiv_ext. 

      apply (IHl' (LocalsD.set locals1 a v') (LocalsD.set locals2 a v') v vs' locals1' locals2' H_In_v_l' H_equiv_ext H_set_all_1 H_set_all_2).
  Qed.      

  (* If variables maps are equivalent up to v, then setting v
  results in equal maps for all variables *)
    Lemma set_preserves_eq_up_to_equiv_v:
    forall locals1 locals2 v value,
      equiv_locals_up_to_v locals1 locals2 v ->
      equiv_locals (LocalsD.set locals1 v value) (LocalsD.set locals2 v value).
    Proof.
      unfold equiv_locals_up_to_v.
      unfold equiv_locals.
      intros locals1 locals2 v value H_equiv_up_to_v.
      intros v'.
      unfold LocalsD.set.
      unfold LocalsD.get.
      destruct (VarID.eqb v' v) eqn:E_v'_eqb_v.
      - rewrite DialectFactsD.eqb_eq. reflexivity.
      - rewrite VarID.eqb_neq_false in E_v'_eqb_v.
        apply (H_equiv_up_to_v v' E_v'_eqb_v).
    Qed.

    Lemma set_preserves_eq_up_to_equiv_any:
    forall locals1 locals2 v a value,
      equiv_locals_up_to_v locals1 locals2 v ->
      equiv_locals_up_to_v (LocalsD.set locals1 a value) (LocalsD.set locals2 a value) v.
    Proof.
      unfold equiv_locals_up_to_v.
      intros locals1 locals2 v a value H_equiv_up_to_v.
      intros v'.
      intro H_neq_v'_v.
      unfold LocalsD.set.
      unfold LocalsD.get.
      destruct (VarID.eqb v' a).
      - rewrite DialectFactsD.eqb_eq. reflexivity.
      - apply (H_equiv_up_to_v v' H_neq_v'_v).
    Qed.

    Lemma set_preserves_eq_up_to_eq_aux:
      forall locals1 locals2 v value,
        equiv_locals (set locals1 v value) (set locals2 v value) ->
        eq_locals (set locals1 v value) (set locals2 v value).
    Proof.
      unfold equiv_locals.
      unfold eq_locals.
      intros locals1 locals2 v value H_equiv.
      intro v'.
      rewrite <- DialectFactsD.eqb_eq.
      apply H_equiv.
    Qed.

    Lemma set_preserves_eq_up_to_eq:
      forall locals1 locals2 v value,
        equiv_locals_up_to_v locals1 locals2 v ->
        (LocalsD.set locals1 v value) = (LocalsD.set locals2 v value).
    Proof.
      intros locals1 locals2 v value H_equiv_up_to_v.
      pose proof (set_preserves_eq_up_to_equiv_v locals1 locals2 v value H_equiv_up_to_v) as H_equiv.
      pose proof (set_preserves_eq_up_to_eq_aux locals1 locals2 v value H_equiv) as H_equiv'.
      unfold eq_locals in H_equiv'.
      apply functional_extensionality in H_equiv'.
      exact H_equiv'.
    Qed.

    Lemma set_all_preserves_eq_up_to_equiv:
    forall l locals1 locals2 v vs locals1' locals2',
      List.In v l ->
        equiv_locals_up_to_v locals1 locals2 v ->
        LocalsD.set_all locals1 l vs = Some locals1' ->
        LocalsD.set_all locals2 l vs = Some locals2' ->
        eq_locals locals1' locals2'.
    Proof.
      induction l as [|a l' IHl'].
      - intros locals1 locals2 v vs locals1' locals2' H_In_v_l.
        contradiction (in_nil H_In_v_l).
      - intros locals1 locals2 v vs locals1' locals2' H_In_v_l.
        intros H_equiv_up_to_v H_set_all_1 H_set_all_2.
        simpl in H_set_all_1.
        simpl in H_set_all_2.
        destruct vs as [|v' vs']; try discriminate.
        pose proof (set_preserves_eq_up_to_eq locals1 locals2 v v' H_equiv_up_to_v) as H_set_equiv.
        
        pose proof (varid_eq_or_neq a v) as H_a_v.
        destruct H_a_v as [H_eq_a_v | H_neq_a_v].

        + rewrite H_eq_a_v in H_set_all_1.
          rewrite H_eq_a_v in H_set_all_2.
          rewrite H_set_equiv in H_set_all_1.
          rewrite H_set_all_1 in H_set_all_2.
          injection H_set_all_2 as H_set_all_2.
          rewrite H_set_all_2.
          unfold eq_locals.
          intros v0.
          reflexivity.
        + pose proof (set_preserves_eq_up_to_equiv_any locals1 locals2 v a v' H_equiv_up_to_v) as H_equiv_up_to_v_a.

          simpl in H_In_v_l.
          destruct H_In_v_l as [H_a_eq_v | H_In_v_l'].
          * contradiction.
          * apply (IHl' (LocalsD.set locals1 a v') (LocalsD.set locals2 a v') v vs' locals1' locals2' H_In_v_l' H_equiv_up_to_v_a H_set_all_1 H_set_all_2).
    Qed.

    Lemma set_all_preserves_eq_up_to_eq:
    forall l locals1 locals2 v vs locals1' locals2',
      List.In v l ->
      equiv_locals_up_to_v locals1 locals2 v ->
      LocalsD.set_all locals1 l vs = Some locals1' ->
      LocalsD.set_all locals2 l vs = Some locals2' ->
      locals1' = locals2'.
    Proof.
      intros l locals1 locals2 v vs locals1' locals2' H_In_v_l H_equiv H_set_all_1 H_set_all_2.
      pose proof (set_all_preserves_eq_up_to_equiv l locals1 locals2 v vs locals1' locals2' H_In_v_l H_equiv H_set_all_1 H_set_all_2) as H_equiv'.
      unfold  eq_locals in H_equiv'.
      unfold get in H_equiv'.
      apply functional_extensionality in H_equiv'.
      exact H_equiv'.
    Qed.

    (* If v is dead after bkw propagation, and it is not in the input
    argument, it must be dead before the bkw propagation already *)
    Lemma not_In_v_fwd:
      forall v s sout instr,
        VarSet.Equal sout (prop_live_set_bkw_instr instr s) ->
        ~ VarSet.In v sout ->
        ~ List.In v instr.(output) ->
        ~ VarSet.In v s.
    Proof.
      intros v s sout instr H_eq_sout H_not_In_v_sout H_not_in_v_output.
      unfold prop_live_set_bkw_instr in H_eq_sout.
      pose proof (not_In_preserves_eq sout (VarSet.union (VarSet.diff s (list_to_set instr.(output))) (list_to_set (extract_yul_vars instr.(input)))) v H_eq_sout H_not_In_v_sout) as H_not_In_v_union.
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

  (* if [set_all] succeeds, it will succeed when changing the assignment *)
  Lemma set_all_some:   
    forall l vs locals1 locals2 locals1',
      LocalsD.set_all locals1 l vs = Some locals1'
    ->
      (exists locals2', LocalsD.set_all locals2 l vs = Some locals2').
  Proof.
    induction l as [|a l' IHl'].
    - intros vs locals1 locals2 locals1'.
      destruct vs as [|v vs'].
      + simpl.
        intros.
        exists locals2.
        reflexivity.
      + intros H.
        simpl in H.
        discriminate H.
    - intros vs locals1 locals2 locals1' H.
      simpl in H.
      simpl.
      destruct vs as [|v vs'].
      + discriminate H.
      + apply (IHl' vs' (LocalsD.set locals1 a v) (LocalsD.set locals2 a v) locals1' H).
  Qed.

  (* if [set_all] fails, it will fail when changing the assignment *)
  Lemma set_all_none:   
    forall l vs locals1 locals2,
      LocalsD.set_all locals1 l vs = None
    ->
     LocalsD.set_all locals2 l vs = None.
  Proof.
    intros l vs locals1 locals2 H.
    destruct (LocalsD.set_all locals2 l vs) as [locals2'|] eqn:E; try reflexivity.
    pose proof (set_all_some l vs locals2 locals1 locals2' E) as H0.
    destruct H0 as [locals1' H0].
    rewrite H0 in H.
    discriminate H.
  Qed.



  (* some tactics used below *)
  Ltac subst_var_by_inj H0 H1 var :=
    rewrite H0 in H1; injection H1 as H1; subst var.

  Ltac destruct_equiv_frames H :=
    assert(H':=H); destruct H' as [H_fname_sf1 [H_bid_sf1 [H_pc_sf1 [H_fname_sf2 [H_bid_sf2 [H_pc_sf2 H_equiv_locals] ]]]]].
  
  Ltac destruct_equiv_states H :=
    assert(H' :=H);  destruct H' as [H_lt_i [H_len_call_stack [H_status [H_dialect [hl [tl [sf1 [sf2 [H_split_i_st1 [H_split_i_st2 H_equiv_sf1_sf2]]]]]]]]]].
  
  Ltac destruct_split_i H tag :=
    let H_lt_i := fresh "H_lt_i_" tag in
    let H_call_stack := fresh "H_call_stack_" tag in 
    let H_len_tl := fresh "H_len_tl_" tag in
    assert( H' :=  H);
    unfold split_at_i in H';
    destruct H' as [H_lt_i [H_call_stack H_len_tl]].
  

  Definition equiv_states_up_to_not_live_v_or_eq_states (p: CFGProgD.t) (i: nat) (fname: FuncName.t) (bid: BlockID.t) (pc: nat) (s: VarSet.t) (st1 st2: StateD.t) (v: VarID.t) :=
    (
      equiv_states_up_to_i_v p i fname bid pc v st1 st2 /\ (* st1 and st2 are equivalent, and *)
        live_at_pc p fname bid pc s /\~ VarSet.In v s (* v is dead *)
    )
    \/
    st2 = st1. (* the states are identical, the easy case ... *)


  Lemma not_live_v_not_in_input_args:
    forall (p: CFGProgD.t) (fname: FuncName.t) (bid: BlockID.t) (b: BlockD.t) (pc: nat) (s: VarSet.t) (instr: InstrD.t)  (v: VarID.t),
      CFGProgD.get_block p fname bid = Some b ->
      CFGProgD.get_instr p fname bid pc = Some instr ->
      live_at_pc p fname bid pc s ->
    ~ VarSet.In v s ->
    ~ In (inl v) instr.(input).
  Proof.
    intros p fname bid b pc s instr v H_b_exists H_pc_get_instr H_live_at_pc H_not_In_v_s.
    pose proof (get_instruction_succ p fname bid b pc instr H_b_exists H_pc_get_instr) as H_pc_lt_len.
 
    (* First branch is eliminated automatically du to contradiction*)
    destruct H_live_at_pc as [fname bid b0 pc s sout H_b0_exists _ H_pc_at_end | fname bid b0 pc s sout instr' H_b0_exists H_live_at_S_pc H_lt_pc H_get_instr' H_sout].


    - (* this case is impossible because we are not at the end of the block *)
      subst_var_by_inj H_b_exists H_b0_exists b0.      
      rewrite H_pc_at_end in H_pc_lt_len. contradiction (Nat.lt_irrefl (length b.(instructions))).
    - subst_var_by_inj H_b_exists H_b0_exists b0.
      unfold prop_live_set_bkw_instr in H_sout.
      pose proof (not_In_preserves_eq sout (VarSet.union (VarSet.diff s (list_to_set (output instr'))) (list_to_set (extract_yul_vars (input instr')))) v H_sout H_not_In_v_s) as H_not_In_v_union.
      rewrite VarSet.union_spec in H_not_In_v_union.
      apply Decidable.not_or in H_not_In_v_union.
      destruct H_not_In_v_union as [_ H_not_In_v_union].
      rewrite <- list_to_set_spec in H_not_In_v_union.
      rewrite <- extract_yul_vars_spec in H_not_In_v_union.
      unfold CFGProgD.get_instr in H_pc_get_instr.
      rewrite H_b_exists in H_pc_get_instr.
      subst_var_by_inj H_pc_get_instr H_get_instr' instr'.
      apply H_not_In_v_union.
  Qed.

  Lemma equiv_states_equiv_dialect:
    forall (p: CFGProgD.t) (i: nat) (fname: FuncName.t) (bid: BlockID.t) (pc: nat)  (st1 st2: StateD.t) (v: VarID.t),
      equiv_states_up_to_i_v p i fname bid pc v st1 st2 ->
      st1.(dialect_state) = st2.(dialect_state).
  Proof.
    intros p i fname bid pc st1 st2 v H_equiv_st1_st2.
    apply H_equiv_st1_st2.
  Qed.

  Lemma equiv_states_equiv_status:
    forall (p: CFGProgD.t) (i: nat) (fname: FuncName.t) (bid: BlockID.t) (pc: nat)  (st1 st2: StateD.t) (v: VarID.t),
      equiv_states_up_to_i_v p i fname bid pc v st1 st2 ->
      st1.(status) = st2.(status).
  Proof.
    intros p i fname bid pc st1 st2 v H_equiv_st1_st2.
    apply H_equiv_st1_st2.
  Qed.

  Lemma live_at_set_status_snd:
    forall (p: CFGProgD.t) (i: nat) (fname: FuncName.t) (bid: BlockID.t) (pc: nat) (s: VarSet.t) (st1 st2 st1': StateD.t) (v: VarID.t) (status: Status.t),
    
      equiv_states_up_to_not_live_v_or_eq_states p i fname bid pc s st1 st2 v ->
      equiv_vars_in_top_frame p st1 st2 ->
      set_status st1 status = st1' ->
      exists st2',
        set_status st2 status = st2' /\
          equiv_states_up_to_not_live_v_or_eq_states p i fname bid pc s st1' st2' v /\
          equiv_vars_in_top_frame p st1' st2'.
    Proof.   
      intros p i fname bid pc s st1 st2 st1' v status.
      intros H_equiv_st1_st2 H_equiv_vars_st1_st2 H_set_status.
      unfold set_status in H_set_status.
      unfold set_status.

      remember {|
          Liveness_snd.StateD.call_stack := call_stack st2;
          Liveness_snd.StateD.status := status;
          Liveness_snd.StateD.dialect_state := dialect_state st2
        |} as st2' eqn:E_st2'.

      exists st2'.

      repeat split; try reflexivity.
      - unfold equiv_states_up_to_not_live_v_or_eq_states.
        unfold equiv_states_up_to_not_live_v_or_eq_states in H_equiv_st1_st2.
        destruct H_equiv_st1_st2 as [H_equiv_st1_st2 | H_equiv_st1_st2].

        + left.
          split.
          * destruct H_equiv_st1_st2 as [H_equiv_st1_st2 [H_live_at H_not_In_v_s]].
            destruct_equiv_states H_equiv_st1_st2.
            repeat split.
            ** rewrite <- H_set_status.
               simpl.
               exact H_lt_i.
            ** rewrite E_st2'.
               rewrite <- H_set_status.
               simpl.
               exact H_len_call_stack.
            ** rewrite E_st2'.
               rewrite <- H_set_status.
               simpl.
               reflexivity.
            ** rewrite E_st2'.
               rewrite <- H_set_status.
               simpl.
               exact H_dialect.
            ** exists hl, tl, sf1, sf2. 
               destruct_split_i H_split_i_st1 st1.
               destruct_split_i H_split_i_st2 st2.
               split.
               *** unfold split_at_i.
                   repeat split.
                   **** rewrite <- H_set_status. simpl. exact H_lt_i_st1.
                   **** rewrite <- H_set_status. simpl. exact H_call_stack_st1.
                   **** exact H_len_tl_st1.
               *** split.
                   ***** unfold split_at_i.
                         repeat split.                 
                         ****** rewrite E_st2'. simpl. exact H_lt_i_st2.
                         ****** rewrite E_st2'. simpl. exact H_call_stack_st2.
                         ****** exact H_len_tl_st2.
                         ***** exact H_equiv_sf1_sf2.

          * destruct H_equiv_st1_st2 as [H_equiv_st1_st2 [H_live_at H_not_In_v_s]].            
            split.
            ** exact H_live_at.
            ** apply H_not_In_v_s.
        + subst st2.
          right.
          rewrite E_st2'.
          rewrite <- H_set_status.
          reflexivity.
      - rewrite E_st2'.
        rewrite <- H_set_status.
        unfold equiv_vars_in_top_frame. simpl.
        exact H_equiv_vars_st1_st2.
    Qed.        
      
  Lemma live_at_set_dialect_snd:
    forall (p: CFGProgD.t) (i: nat) (fname: FuncName.t) (bid: BlockID.t) (pc: nat) (s: VarSet.t) (st1 st2 st1': StateD.t) (v: VarID.t) (dialect: D.dialect_state_t),
    
      equiv_states_up_to_not_live_v_or_eq_states p i fname bid pc s st1 st2 v ->
      equiv_vars_in_top_frame p st1 st2 ->
      set_dialect_state st1 dialect = st1' ->
      exists st2',
        set_dialect_state st2 dialect = st2' /\
          equiv_states_up_to_not_live_v_or_eq_states p i fname bid pc s st1' st2' v /\
          equiv_vars_in_top_frame p st1' st2'.
    Proof.   
      intros p i fname bid pc s st1 st2 st1' v dialect.
      intros H_equiv_st1_st2 H_equiv_vars_st1_st2 H_set_dialect.
      unfold set_dialect_state in H_set_dialect.
      unfold set_dialect_state.

      remember {|
          Liveness_snd.StateD.call_stack := call_stack st2;
          Liveness_snd.StateD.status := status st2;
          Liveness_snd.StateD.dialect_state := dialect
        |} as st2' eqn:E_st2'.

      exists st2'.

      repeat split; try reflexivity.
      - unfold equiv_states_up_to_not_live_v_or_eq_states.
        unfold equiv_states_up_to_not_live_v_or_eq_states in H_equiv_st1_st2.
        destruct H_equiv_st1_st2 as [H_equiv_st1_st2 | H_equiv_st1_st2].

        + left.
          split.
          * destruct H_equiv_st1_st2 as [H_equiv_st1_st2 [H_live_at H_not_In_v_s]].
            destruct_equiv_states H_equiv_st1_st2.
            repeat split.
            ** rewrite <- H_set_dialect.
               simpl.
               exact H_lt_i.
            ** rewrite E_st2'.
               rewrite <- H_set_dialect.
               simpl.
               exact H_len_call_stack.
            ** rewrite E_st2'.
               rewrite <- H_set_dialect.
               simpl.
               exact H_status.
            ** rewrite E_st2'.
               rewrite <- H_set_dialect.
               simpl.
               reflexivity.
            ** exists hl, tl, sf1, sf2. 
               destruct_split_i H_split_i_st1 st1.
               destruct_split_i H_split_i_st2 st2.
               split.
               *** unfold split_at_i.
                   repeat split.
                   **** rewrite <- H_set_dialect. simpl. exact H_lt_i_st1.
                   **** rewrite <- H_set_dialect. simpl. exact H_call_stack_st1.
                   **** exact H_len_tl_st1.
               *** split.
                   ***** unfold split_at_i.
                         repeat split.                 
                         ****** rewrite E_st2'. simpl. exact H_lt_i_st2.
                         ****** rewrite E_st2'. simpl. exact H_call_stack_st2.
                         ****** exact H_len_tl_st2.
                         ***** exact H_equiv_sf1_sf2.

          * destruct H_equiv_st1_st2 as [H_equiv_st1_st2 [H_live_at H_not_In_v_s]].            
            split.
            ** exact H_live_at.
            ** apply H_not_In_v_s.
        + subst st2.
          right.
          rewrite E_st2'.
          rewrite <- H_set_dialect.
          reflexivity.
      - rewrite E_st2'.
        rewrite <- H_set_dialect.
        unfold equiv_vars_in_top_frame. simpl.
        exact H_equiv_vars_st1_st2.
    Qed.        


    Lemma live_at_error_1_snd:
    forall (p: CFGProgD.t) (i: nat) (fname: FuncName.t) (bid: BlockID.t) (b: BlockD.t) (pc: nat) (s: VarSet.t) (st1 st2 st1': StateD.t) (v: VarID.t) (msg: string),
      CFGProgD.get_block p fname bid = Some b ->
      live_at_pc p fname bid pc s ->
      equiv_states_up_to_i_v p i fname bid pc v st1 st2 ->
      error st1 msg = st1' ->
      ~ VarSet.In v s ->
        exists st2' bid' pc' s',
          error st2 msg = st2'
          /\
            equiv_states_up_to_not_live_v_or_eq_states p i fname bid' pc' s' st1' st2' v (* we reach state equivalent to st1' *)
          /\
            equiv_vars_in_top_frame p st1' st2'. (* the top frames are equivalent wrt the accessed variables *)
    Proof.
      intros p i fname bid b pc s st1 st2 st1' v msg.
      intros H_b_exists H_live_at_pc H_equiv_st1_st2 H_error_st1 H_not_In_v_s.
      unfold error in H_error_st1.
      unfold error.
      unfold set_status in H_error_st1.
      unfold set_status.
      remember {|
          Liveness_snd.StateD.call_stack := call_stack st2;
          Liveness_snd.StateD.status := Status.Error msg;
          Liveness_snd.StateD.dialect_state := dialect_state st2
        |} as st2' eqn:E_st2'.
      exists st2', bid, pc, s.
      repeat split.
      - rewrite E_st2'.
        rewrite <- H_error_st1.
        unfold equiv_states_up_to_not_live_v_or_eq_states.
        left.
        destruct_equiv_states H_equiv_st1_st2.
        unfold equiv_states_up_to_i_v.
        simpl.
        repeat split; try assumption.
        exists hl, tl, sf1, sf2.
        split.
        + apply H_split_i_st1.
        + split.
          * apply H_split_i_st2.
          * apply H_equiv_sf1_sf2.
      - pose proof (equiv_state_equiv_frames_at_top p fname bid b pc i v s st1 st2 H_b_exists H_live_at_pc H_not_In_v_s H_equiv_st1_st2) as H_equiv_top_frames_st1_st2.

        rewrite E_st2'.
        rewrite <- H_error_st1.
        
        unfold equiv_vars_in_top_frame in H_equiv_top_frames_st1_st2.
        simpl in H_equiv_top_frames_st1_st2.
        unfold equiv_vars_in_top_frame.
        simpl.
 
        destruct (call_stack st1); destruct (call_stack st2); try destruct H_equiv_top_frames_st1_st2 as [_H1 [H2 [H3 H4]]]; repeat split; try (reflexivity || assumption).        
    Qed.

    Lemma app_nil_hd:
      forall {A: Type} (x y: A) (l l' l'': list A),
        length l = length l' ->
        [] ++ x :: l = l'' ++ y :: l' ->
        l'' = [].
    Proof.
      intros A x y l l' l'' H_len H.            
      pose proof (Misc.len_eq ([] ++ x :: l ) (l'' ++ y :: l') H) as H_len_eq.
      simpl in H_len_eq.
      rewrite length_app in H_len_eq.
      simpl in H_len_eq.            
      rewrite H_len in H_len_eq.
      apply n_eq_n_plus_m in H_len_eq.
      apply nil_length_inv in H_len_eq.
      exact  H_len_eq.
    Qed.

  Lemma live_at_exec_assignment_1_snd:
    forall (p: CFGProgD.t) (i: nat) (fname: FuncName.t) (bid: BlockID.t) (b: BlockD.t) (pc: nat) (s: VarSet.t) (instr: InstrD.t) (st1 st2 st1': StateD.t) (sf1 sf2: StackFrameD.t) (tl: CallStackD.t) (values: list D.value_t) (v: VarID.t),
      CFGProgD.get_block p fname bid = Some b ->
      SmallStepD.get_next_instr st1 p = Some instr ->
      live_at_pc p fname bid pc s ->
      equiv_states_up_to_i_v p i fname bid pc v st1 st2 ->
      split_at_i i st1.(call_stack) [] tl sf1 ->
      split_at_i i st2.(call_stack) [] tl sf2 ->
      execute_assignment p values instr.(output) sf1 tl st1 = st1' ->
      ~ VarSet.In v s ->
        exists st2' bid' pc' s',
          execute_assignment p values instr.(output) sf2 tl st2 = st2'
          /\
            equiv_states_up_to_not_live_v_or_eq_states p i fname bid' pc' s' st1' st2' v (* we reach state equivalent to st1' *)
          /\
            equiv_vars_in_top_frame p st1' st2'. (* the top frames are equivalent wrt the accessed variables *)
  Proof.
    intros p i fname bid b pc s instr st1 st2 st1' sf1 sf2 tl values v.
    intros H_b_exists H_get_instr H_live_at_pc H_equiv_st1_st2 H_split_i_st1 H_split_i_st2 H_exec_assign H_not_In_v_s.
 
    unfold execute_assignment in H_exec_assign.
    unfold execute_assignment.

    (* split on wether set_all succeed *)
    destruct (set_all (locals sf1) (output instr) values) as [locals'_sf1|] eqn:H_locals'_sf1.

    (* set�all succeeded, the other case is easy and it comes afterwards *)
    - (* since set�all succeeded with sf1 it will also succeed with sf2 *)
      pose proof (set_all_some (output instr) values sf1.(locals) sf2.(locals) locals'_sf1 H_locals'_sf1) as [locals'_sf2 H_locals'_sf2].
      rewrite H_locals'_sf2.

      (* Now we can construct st2' *)
      remember {|
                 Liveness_snd.StateD.call_stack :=
                 {|
                   Liveness_snd.StackFrameD.fname := StackFrameD.fname sf2;
                   Liveness_snd.StackFrameD.locals := locals'_sf2;
                   Liveness_snd.StackFrameD.curr_bid := curr_bid sf2;
                   Liveness_snd.StackFrameD.pc := StackFrameD.pc sf2 + 1
                 |} :: tl;
                 Liveness_snd.StateD.status := status st2;
                 Liveness_snd.StateD.dialect_state := dialect_state st2
        |} as st2' eqn:E_st2'.

      (* destruct equivalence facts *)
      assert(H_equiv_st1_st2' := H_equiv_st1_st2).
      destruct H_equiv_st1_st2' as [H_lt_i [H_len_call_stack [H_status [H_dialect [hl' [tl' [sf1' [sf2' [H_split_i_st1' [H_split_i_st2' H_equiv_sf1_sf2']]]]]]]]]].
      destruct_equiv_frames H_equiv_sf1_sf2'.
      destruct_split_i H_split_i_st1 st1.
      destruct_split_i H_split_i_st2 st2.
      destruct_split_i H_split_i_st1' st1'.
      destruct_split_i H_split_i_st2' st2'.

      rewrite <- H_len_tl_st2' in H_len_tl_st2.
      rewrite H_call_stack_st1 in H_call_stack_st1'.

      (* substitute  hl' by [] *)
      pose proof (app_nil_hd sf1 sf1' tl tl' hl' H_len_tl_st2 H_call_stack_st1') as H_hl'.
      subst hl'.
      simpl in H_call_stack_st1'.
      injection H_call_stack_st1' as H_sf1' H_tl.
      subst sf1'.
      subst tl'.
      rewrite H_call_stack_st2 in H_call_stack_st2'.          
      simpl in H_call_stack_st2'.
      injection H_call_stack_st2' as H_sf2'.
      subst sf2'.

      (* a version og get_block with sf1.(fname) and sf1.(bid), will be needed later in several places *)
      assert( H_b_exists' :=  H_b_exists ).
      rewrite <- H_fname_sf1 in  H_b_exists'.
      rewrite <- H_bid_sf1 in  H_b_exists'.

      (* get nth_err from get_instr, will be needed later in several places *)
      assert(H_get_instr_nth := H_get_instr).
      unfold get_next_instr in H_get_instr_nth.
      rewrite H_call_stack_st1 in H_get_instr_nth.
      simpl in H_get_instr_nth.
      unfold get_instr in H_get_instr_nth.
      rewrite H_fname_sf1 in H_get_instr_nth.
      rewrite H_bid_sf1 in H_get_instr_nth.
      rewrite H_b_exists in H_get_instr_nth.
      rewrite H_pc_sf1 in H_get_instr_nth.

      (* infe pc<length b.(instructions), which is needed to eliminate cases in which pc=length b.(instructions) *)
      pose proof (get_next_instruction_succ st1 p instr sf1 tl b H_call_stack_st1 H_b_exists' H_get_instr) as H_pc_is_not_at_end.

      (* destruc live_at_pc, then eliminate the first case *)
      assert(H_live_at_pc' := H_live_at_pc).
      destruct H_live_at_pc' as [fname bid b0 pc s sout H_b0_exists _ H_pc_at_end | fname bid b0 pc s sout instr' H_b0_exists H_live_at_S_pc H_lt_pc H_get_instr' H_sout].

      + (* this case is imposible *)
        rewrite H_pc_sf1 in H_pc_is_not_at_end.
        subst_var_by_inj H_b_exists H_b0_exists b0.
        rewrite H_pc_at_end in H_pc_is_not_at_end.
        contradiction (Nat.lt_irrefl (length (instructions b))).

      + subst_var_by_inj H_b_exists H_b0_exists b0.

        rewrite H_get_instr_nth in H_get_instr'.
        injection H_get_instr' as H_get_instr'.
        subst instr'.
        
        exists st2', bid, (S pc), s.
        repeat split; try reflexivity.
        * rewrite E_st2'.
          rewrite <- H_exec_assign.
          unfold equiv_states_up_to_not_live_v_or_eq_states.

          (* now we split on wether v in the output variables *)
          pose proof (varlist_in_dec instr.(output) v) as H_v_output.

          destruct H_v_output as [H_v_in_output | H_v_not_in_output].

          (*  v is in the output variables *)
          ** right.
             unfold equiv_states_up_to_i_v in H_equiv_st1_st2.
             
             rewrite H_fname_sf1, H_bid_sf1, H_pc_sf1, H_fname_sf2, H_bid_sf2, H_pc_sf2.

             rewrite <- (set_all_preserves_eq_up_to_eq instr.(output) sf1.(locals) sf2.(locals) v values locals'_sf1 locals'_sf2 H_v_in_output H_equiv_locals H_locals'_sf1 H_locals'_sf2).
             rewrite H_dialect.
             rewrite H_status.
             reflexivity.

          (*  v is not in the output variables *)
          ** left.
             unfold equiv_states_up_to_i_v.
             simpl.
             
             repeat split.
             *** rewrite H_len_tl_st1. lia.
             *** apply H_status.
             *** apply H_dialect.
             *** exists [], tl.
                 exists {|
                     Liveness_snd.StackFrameD.fname := StackFrameD.fname sf1;
                     Liveness_snd.StackFrameD.locals := locals'_sf1;
                     Liveness_snd.StackFrameD.curr_bid := curr_bid sf1;
                     Liveness_snd.StackFrameD.pc := StackFrameD.pc sf1 + 1
                   |}.
                 exists {|
                     Liveness_snd.StackFrameD.fname := StackFrameD.fname sf2;
                     Liveness_snd.StackFrameD.locals := locals'_sf2;
                     Liveness_snd.StackFrameD.curr_bid := curr_bid sf2;
                     Liveness_snd.StackFrameD.pc := StackFrameD.pc sf2 + 1
                   |}.
                 unfold split_at_i.
             simpl.
             repeat split.
             **** rewrite H_len_tl_st1. lia.
             **** exact H_len_tl_st2'.
             **** rewrite H_len_tl_st1. lia.
             **** exact H_len_tl_st2'.
             **** simpl. exact H_fname_sf1.
             **** simpl. exact H_bid_sf1.
             **** simpl. rewrite H_pc_sf1. rewrite Nat.add_comm. simpl. reflexivity.
             **** simpl. exact H_fname_sf2.
             **** simpl. exact H_bid_sf2.
             **** simpl. rewrite H_pc_sf2. rewrite Nat.add_comm. simpl. reflexivity.
             **** unfold equiv_locals_up_to_v.
                  simpl.
                  apply (set_all_preserves_eq_up_to instr.(output) sf1.(locals) sf2.(locals) v values locals'_sf1 locals'_sf2 H_v_not_in_output H_equiv_locals H_locals'_sf1 H_locals'_sf2).
                 
        *** apply H_live_at_S_pc.
        *** exact (not_In_v_fwd v s sout instr H_sout H_not_In_v_s H_v_not_in_output).
        * rewrite E_st2'.
          rewrite <- H_exec_assign.
          unfold equiv_vars_in_top_frame.
          simpl.
          repeat split.
          ** rewrite H_fname_sf1. rewrite H_fname_sf2. reflexivity.
          ** rewrite H_bid_sf1. rewrite H_bid_sf2. reflexivity.
          ** rewrite H_pc_sf1. rewrite H_pc_sf2. reflexivity.
          ** intros v0 s0 b_top H_b_top_exists H_accessed_vars H_in_v0_s0.
             rewrite H_fname_sf1 in  H_b_top_exists.
             rewrite H_bid_sf1 in  H_b_top_exists.
             subst_var_by_inj H_b_exists H_b_top_exists b_top.

             (* wether v in output or not *)
             pose proof (varlist_in_dec instr.(output) v) as H_v_output.
             destruct H_v_output as [H_v_in_output | H_v_not_in_output].

             *** rewrite (set_all_preserves_eq_up_to_eq instr.(output) sf1.(locals) sf2.(locals) v values locals'_sf1 locals'_sf2 H_v_in_output H_equiv_locals H_locals'_sf1 H_locals'_sf2).
                 rewrite DialectFactsD.eqb_eq.
                 reflexivity.
                 
             *** pose proof (not_In_v_fwd v s sout instr H_sout H_not_In_v_s H_v_not_in_output) as H_not_In_v_s'.
                 rewrite H_pc_sf1 in H_accessed_vars.
                 rewrite Nat.add_comm in H_accessed_vars.
                 pose proof (accessed_var_instr_neq_v p fname bid b (S pc) s0 v0 s v H_b_exists H_live_at_S_pc H_not_In_v_s' H_accessed_vars H_in_v0_s0) as H_v0_neq_v.                 
                 apply (set_all_preserves_eq_up_to instr.(output) sf1.(locals) sf2.(locals) v values locals'_sf1 locals'_sf2 H_v_not_in_output H_equiv_locals H_locals'_sf1 H_locals'_sf2).
                 exact H_v0_neq_v.

    (* set�all failed *)
    - rewrite (set_all_none (output instr) values sf1.(locals) sf2.(locals) H_locals'_sf1).
      apply (live_at_error_1_snd p i fname bid b pc s st1 st2 st1' v "Mismatch length in output variables and input values" H_b_exists H_live_at_pc H_equiv_st1_st2 H_exec_assign H_not_In_v_s).
  Qed.

  Lemma append_same_len {A: Type}:
  forall (l l1 l1' l2 l2': list A),
    length l1' = length l2' ->
    l = l1++l1' ->
    l = l2++l2' ->
    l1' = l2' /\ l1 = l2.
  Proof.
    induction l as [|a l' IHl'].
    - intros l1 l1' l2 l2' H_len H_eq1 H_eq2.
      destruct l1; destruct l2; try discriminate; try reflexivity.
      simpl in H_eq1, H_eq2.
      rewrite <- H_eq1, H_eq2.
      split; reflexivity.
    - intros l1 l1' l2 l2' H_len H_eq1 H_eq2.
      destruct l1; destruct l2; try discriminate.
      + simpl in H_eq1, H_eq2.
        rewrite <- H_eq1, H_eq2.
        split; reflexivity.
      + simpl in H_eq1, H_eq2.
        rewrite H_eq1 in H_eq2.
        apply Misc.len_eq in H_eq2.
        rewrite H_len in H_eq2.
        simpl in H_eq2.
        rewrite length_app in H_eq2.
        lia. (* contradiction *)
      + simpl in H_eq1, H_eq2.
        rewrite H_eq2 in H_eq1.
        apply Misc.len_eq in H_eq1.
        rewrite <- H_len in H_eq1.
        simpl in H_eq1.
        rewrite length_app in H_eq1.
        lia. (* contradiction *)
      + simpl in H_eq1, H_eq2.
        injection H_eq1 as H_a_1 H_l'_1.
        injection H_eq2 as H_a_2 H_l'_2.
        pose proof (IHl' l1 l1' l2 l2' H_len H_l'_1 H_l'_2) as [H_l H_r].
        rewrite <- H_a_1, <- H_a_2.
        rewrite <- H_l, H_r.
        split; reflexivity.
  Qed.


  Lemma split_on_same_i {A: Type}:
    forall (i: nat) (l hl1 hl2 tl1 tl2: list A) (x1 x2: A),
      split_at_i i l hl1 tl1 x1 ->
      split_at_i i l hl2 tl2 x2 ->
      hl1 = hl2 /\ tl1 = tl2 /\ x1 = x2.
    Proof.
      intros i l hl1 hl2 tl1 tl2 x1 x2 H_split_l1 H_split_l2.
      unfold split_at_i in H_split_l1.
      unfold split_at_i in H_split_l2.

      destruct H_split_l1 as [H_lt_i1 [H_call_stack1 H_len_tl1]].
      destruct H_split_l2 as [H_lt_i2 [H_call_stack2 H_len_tl2]].

      assert(H_len: length (x1 :: tl1) = length (x2 :: tl2)). simpl. lia.

      pose proof (append_same_len l hl1 (x1::tl1) hl2 (x2::tl2) H_len H_call_stack1 H_call_stack2) as H_app.
      destruct H_app as [H1 H2] .
      injection H1 as H10 H11.
      split; try split; try assumption.
    Qed.







  Lemma live_at_exec_assignment_2_snd:
    forall (p: CFGProgD.t) (i: nat) (fname: FuncName.t) (bid: BlockID.t) (b: BlockD.t) (pc: nat) (s: VarSet.t) (instr: InstrD.t) (st1 st2 st1': StateD.t) (top_sf sf1 sf2: StackFrameD.t) (hl tl: CallStackD.t) (values: list D.value_t) (v: VarID.t),
      CFGProgD.get_block p fname bid = Some b ->
      SmallStepD.get_next_instr st1 p = Some instr ->
      live_at_pc p fname bid pc s ->
      equiv_states_up_to_i_v p i fname bid pc v st1 st2 ->
      split_at_i i st1.(call_stack) (top_sf::hl) tl sf1 ->
      split_at_i i st2.(call_stack) (top_sf::hl) tl sf2 ->
      execute_assignment p values instr.(output) top_sf (hl++(sf1::tl)) st1 = st1' ->
      ~ VarSet.In v s ->
        exists st2' bid' pc' s',
          execute_assignment p values instr.(output) top_sf (hl++(sf2::tl)) st2 = st2'
          /\
            equiv_states_up_to_not_live_v_or_eq_states p i fname bid' pc' s' st1' st2' v (* we reach state equivalent to st1' *)
          /\
            equiv_vars_in_top_frame p st1' st2'. (* the top frames are equivalent wrt the accessed variables *)
    Proof.  
    intros p i fname bid b pc s instr st1 st2 st1' top_sf sf1 sf2 hl tl values v.
    intros H_b_exists H_get_instr H_live_at_pc H_equiv_st1_st2 H_split_i_st1 H_split_i_st2 H_exec_assign H_not_In_v_s.
 
    unfold execute_assignment in H_exec_assign.
    unfold execute_assignment.

    (* split on wether set_all succeed *)
    destruct (set_all (locals top_sf) (output instr) values) as [locals'_sf1|] eqn:H_locals'_sf1.

     (* set�all succeeded, the other case is easy and it comes afterwards *)
    - remember {|
                 Liveness_snd.StateD.call_stack :=
                {|
                   Liveness_snd.StackFrameD.fname := StackFrameD.fname top_sf;
                   Liveness_snd.StackFrameD.locals := locals'_sf1;
                   Liveness_snd.StackFrameD.curr_bid := curr_bid top_sf;
                   Liveness_snd.StackFrameD.pc := StackFrameD.pc top_sf + 1
                |} :: hl ++ sf2 :: tl;
                 Liveness_snd.StateD.status := status st2;
                Liveness_snd.StateD.dialect_state := dialect_state st2
              |} as st2' eqn:E_st2'.

      (* destruct equivalence facts *)
      assert(H_equiv_st1_st2' := H_equiv_st1_st2).
      destruct H_equiv_st1_st2' as [H_lt_i [H_len_call_stack [H_status [H_dialect [hl' [tl' [sf1' [sf2' [H_split_i_st1' [H_split_i_st2' H_equiv_sf1_sf2']]]]]]]]]].
      destruct_equiv_frames H_equiv_sf1_sf2'.
      destruct_split_i H_split_i_st1 st1.
      destruct_split_i H_split_i_st2 st2.
      destruct_split_i H_split_i_st1' st1'.
      destruct_split_i H_split_i_st2' st2'.
      pose proof (split_on_same_i i (call_stack st1) (top_sf :: hl) hl' tl tl' sf1 sf1' H_split_i_st1 H_split_i_st1') as H_split_st1_facts.
      pose proof (split_on_same_i i (call_stack st2) (top_sf :: hl) hl' tl tl' sf2 sf2' H_split_i_st2 H_split_i_st2') as H_split_st2_facts.
      destruct H_split_st1_facts as [H_hl1_eq [H_tl1_eq H_sf1_eq]].
      destruct H_split_st2_facts as [H_hl2_eq [H_tl2_eq H_sf2_eq]].
      subst hl' tl' sf1' sf2'.

      exists st2', bid, pc, s.
      split; try reflexivity.
      split.
      + rewrite  E_st2'.
       
        rewrite <- H_exec_assign.
        unfold equiv_states_up_to_i_v.

        (* now we split on wether v in the output variables *)

        unfold equiv_states_up_to_not_live_v_or_eq_states.
        left.
        unfold equiv_states_up_to_i_v.
        simpl.

        repeat split; try assumption.
       * rewrite length_app.
         simpl.
         rewrite H_len_tl_st2'.
         lia.
      * repeat rewrite length_app.
        simpl.    
        reflexivity.
      * exists ({|
                   Liveness_snd.StackFrameD.fname := StackFrameD.fname top_sf;
                   Liveness_snd.StackFrameD.locals := locals'_sf1;
                   Liveness_snd.StackFrameD.curr_bid := curr_bid top_sf;
                   Liveness_snd.StackFrameD.pc := StackFrameD.pc top_sf + 1
                |}::hl).
        exists tl, sf1, sf2.
        repeat split; try assumption.
        ** simpl.
           rewrite length_app.
           simpl.
           rewrite H_len_tl_st2'.
           lia.
        ** simpl.
           rewrite length_app.
           simpl.
           rewrite H_len_tl_st2'.
           lia.
    + rewrite  E_st2'.
      rewrite <- H_exec_assign.
      unfold equiv_vars_in_top_frame.
      simpl.
      repeat split; try reflexivity.
      intros.
      rewrite DialectFactsD.eqb_eq.  
      reflexivity. 
     
     (* set�all failed *)
    - apply (live_at_error_1_snd p i fname bid b pc s st1 st2 st1' v "Mismatch length in output variables and input values" H_b_exists H_live_at_pc H_equiv_st1_st2 H_exec_assign H_not_In_v_s).
  Qed.


  Lemma live_at_exec_opcode_1_snd:
    forall (p: CFGProgD.t) (i: nat) (fname: FuncName.t) (bid: BlockID.t) (b: BlockD.t) (pc: nat) (s: VarSet.t) (instr: InstrD.t) (opcode: D.opcode_t) (st1 st2 st1': StateD.t) (sf1 sf2: StackFrameD.t) (tl: CallStackD.t) (values: list D.value_t) (v: VarID.t),
      CFGProgD.get_block p fname bid = Some b ->
      SmallStepD.get_next_instr st1 p = Some instr ->
      live_at_pc p fname bid pc s ->
      equiv_states_up_to_i_v p i fname bid pc v st1 st2 ->
      split_at_i i st1.(call_stack) [] tl sf1 ->
      split_at_i i st2.(call_stack) [] tl sf2 ->
      execute_opcode p opcode values instr.(output) sf1 tl st1 = st1' ->
      ~ VarSet.In v s ->
        exists st2' bid' pc' s',
          execute_opcode p opcode values instr.(output) sf2 tl st2 = st2'
          /\
            equiv_states_up_to_not_live_v_or_eq_states p i fname bid' pc' s' st1' st2' v (* we reach state equivalent to st1' *)
          /\
            equiv_vars_in_top_frame p st1' st2'. (* the top frames are equivalent wrt the accessed variables *)
  Proof.
    intros p i fname bid b pc s instr opcode st1 st2 st1' sf1 sf2 tl values v.
    intros H_b_exists H_get_instr H_live_at_pc H_equiv_st1_st2 H_split_i_st1 H_split_i_st2 H_exec_opcode H_not_In_v_s.
    unfold execute_opcode in H_exec_opcode.
    unfold execute_opcode.

    rewrite <- (equiv_states_equiv_dialect p i fname bid pc st1 st2 v H_equiv_st1_st2).
    destruct (D.execute_opcode (dialect_state st1) opcode values) as [[out_vals_st1 dialect_state_st1] status_st1] eqn:E_D_exec_opcode.
        
    remember (execute_assignment p out_vals_st1 (output instr) sf1 tl st1) as st1_aux eqn:E_exec_assign_st1.
    symmetry in E_exec_assign_st1. 
     
    pose proof (live_at_exec_assignment_1_snd p i fname bid b pc s instr st1 st2 st1_aux sf1 sf2 tl out_vals_st1 v H_b_exists H_get_instr H_live_at_pc H_equiv_st1_st2 H_split_i_st1 H_split_i_st2 E_exec_assign_st1 H_not_In_v_s) as [st2_aux' [bid' [pc' [s' [H_exec_assign_st2 [H_equiv_st1_aux_st2_aux' H_equiv_vars_st1_aux_st2_aux']]]]]].

    rewrite H_exec_assign_st2.
   
    remember (set_dialect_state st1_aux dialect_state_st1) as st1_aux' eqn:E_set_dialect.
    symmetry in E_set_dialect.
    
    pose proof (live_at_set_dialect_snd p i fname bid' pc' s' st1_aux  st2_aux' st1_aux' v dialect_state_st1 H_equiv_st1_aux_st2_aux' H_equiv_vars_st1_aux_st2_aux' E_set_dialect) as [st2_aux'' [H_set_dialect_st2 [H_equiv_st1_aux'_st2_aux'' H_equiv_vars_st1_aux'_st2_aux'']]].

    rewrite H_set_dialect_st2.
    
    pose proof (live_at_set_status_snd p i fname bid' pc' s' st1_aux' st2_aux'' st1' v  status_st1 H_equiv_st1_aux'_st2_aux'' H_equiv_vars_st1_aux'_st2_aux'' H_exec_opcode) as [st2' H].

    exists st2', bid', pc', s'.
    apply H.
  Qed.

  Lemma live_at_exec_opcode_2_snd:
    forall (p: CFGProgD.t) (i: nat) (fname: FuncName.t) (bid: BlockID.t) (b: BlockD.t) (pc: nat) (s: VarSet.t) (instr: InstrD.t) (opcode: D.opcode_t) (st1 st2 st1': StateD.t) (top_sf sf1 sf2: StackFrameD.t) (hl tl: CallStackD.t) (values: list D.value_t) (v: VarID.t),
      CFGProgD.get_block p fname bid = Some b ->
      SmallStepD.get_next_instr st1 p = Some instr ->
      live_at_pc p fname bid pc s ->
      equiv_states_up_to_i_v p i fname bid pc v st1 st2 ->
      split_at_i i st1.(call_stack) (top_sf::hl) tl sf1 ->
      split_at_i i st2.(call_stack) (top_sf::hl) tl sf2 ->
      execute_opcode p opcode values instr.(output) top_sf (hl++(sf1::tl)) st1 = st1' ->
      ~ VarSet.In v s ->
        exists st2' bid' pc' s',
          execute_opcode p opcode values instr.(output) top_sf (hl++(sf2::tl)) st2 = st2'
          /\
            equiv_states_up_to_not_live_v_or_eq_states p i fname bid' pc' s' st1' st2' v (* we reach state equivalent to st1' *)
          /\
            equiv_vars_in_top_frame p st1' st2'. (* the top frames are equivalent wrt the accessed variables *)
  Proof.
    intros p i fname bid b pc s instr opcode st1 st2 st1' top_sf sf1 sf2 hl' tl values v.
    intros H_b_exists H_get_instr H_live_at_pc H_equiv_st1_st2 H_split_i_st1 H_split_i_st2 H_exec_opcode H_not_In_v_s.
    unfold execute_opcode in H_exec_opcode.
    unfold execute_opcode.

    rewrite <- (equiv_states_equiv_dialect p i fname bid pc st1 st2 v H_equiv_st1_st2).
    destruct (D.execute_opcode (dialect_state st1) opcode values) as [[out_vals_st1 dialect_state_st1] status_st1] eqn:E_D_exec_opcode.
        
    remember (execute_assignment p out_vals_st1 (output instr) top_sf (hl' ++ sf1 :: tl) st1) as st1_aux eqn:E_exec_assign_st1.
    symmetry in E_exec_assign_st1.
     
    pose proof (live_at_exec_assignment_2_snd p i fname bid b pc s instr st1 st2 st1_aux top_sf sf1 sf2 hl' tl out_vals_st1 v H_b_exists H_get_instr H_live_at_pc H_equiv_st1_st2 H_split_i_st1 H_split_i_st2 E_exec_assign_st1 H_not_In_v_s) as [st2_aux' [bid' [pc' [s' [H_exec_assign_st2 [H_equiv_st1_aux_st2_aux' H_equiv_vars_st1_aux_st2_aux']]]]]].

    rewrite H_exec_assign_st2.
   
    remember (set_dialect_state st1_aux dialect_state_st1) as st1_aux' eqn:E_set_dialect.
    symmetry in E_set_dialect.
    
    pose proof (live_at_set_dialect_snd p i fname bid' pc' s' st1_aux  st2_aux' st1_aux' v dialect_state_st1 H_equiv_st1_aux_st2_aux' H_equiv_vars_st1_aux_st2_aux' E_set_dialect) as [st2_aux'' [H_set_dialect_st2 [H_equiv_st1_aux'_st2_aux'' H_equiv_vars_st1_aux'_st2_aux'']]].

    rewrite H_set_dialect_st2.
    
    pose proof (live_at_set_status_snd p i fname bid' pc' s' st1_aux' st2_aux'' st1' v  status_st1 H_equiv_st1_aux'_st2_aux'' H_equiv_vars_st1_aux'_st2_aux'' H_exec_opcode) as [st2' H].

    exists st2', bid', pc', s'.
    apply H.
  Qed.


  Lemma live_at_exec_func_1_snd:
    forall (p: CFGProgD.t) (i: nat) (fname: FuncName.t) (bid: BlockID.t) (b: BlockD.t) (pc: nat) (s: VarSet.t) (instr: InstrD.t) (func_name: FuncName.t) (st1 st2 st1': StateD.t) (sf1 sf2: StackFrameD.t) (tl: CallStackD.t) (values: list D.value_t) (v: VarID.t),
      CFGProgD.get_block p fname bid = Some b ->
      SmallStepD.get_next_instr st1 p = Some instr ->
      live_at_pc p fname bid pc s ->
      equiv_states_up_to_i_v p i fname bid pc v st1 st2 ->
      split_at_i i st1.(call_stack) [] tl sf1 ->
      split_at_i i st2.(call_stack) [] tl sf2 ->
      execute_func p func_name values instr.(output) sf1 tl st1 = st1' ->
      ~ VarSet.In v s ->
        exists st2' bid' pc' s',
          execute_func p func_name values instr.(output) sf2 tl st2 = st2'
          /\
            equiv_states_up_to_not_live_v_or_eq_states p i fname bid' pc' s' st1' st2' v (* we reach state equivalent to st1' *)
          /\
            equiv_vars_in_top_frame p st1' st2'. (* the top frames are equivalent wrt the accessed variables *)
  Proof.
    intros p i fname bid b pc s instr func_name st1 st2 st1' sf1 sf2 tl values v.
    intros H_b_exists H_get_instr H_live_at_pc H_equiv_st1_st2 H_split_i_st1 H_split_i_st2 H_exec_func H_not_In_v_s.
    unfold execute_func in H_exec_func.
    unfold execute_func.

    (* split on wether the function exists *)
    destruct (get_func p func_name) as [func|] eqn:E_get_func.
    
    (* function exists *)
    - destruct (set_all LocalsD.empty (args func) values) as [locals'|] eqn:H_set_all.

      (* set_all succeeded *)
      + remember {|
          Liveness_snd.StateD.call_stack :=
          {|
            Liveness_snd.StackFrameD.fname := StackFrameD.fname sf2;
            Liveness_snd.StackFrameD.locals := locals';
            Liveness_snd.StackFrameD.curr_bid := entry_bid func;
            Liveness_snd.StackFrameD.pc := 0
          |} :: sf2 :: tl;
        Liveness_snd.StateD.status := status st2;
        Liveness_snd.StateD.dialect_state := dialect_state st2
      |} as st2' eqn:E_st2'.

      exists st2', bid, pc, s.

      assert(H_equiv_st1_st2' := H_equiv_st1_st2).
      destruct H_equiv_st1_st2' as [H_lt_i [H_len_call_stack [H_status [H_dialect [hl' [tl' [sf1' [sf2' [H_split_i_st1' [H_split_i_st2' H_equiv_sf1_sf2']]]]]]]]]].
      destruct_equiv_frames H_equiv_sf1_sf2'.

      pose proof (split_on_same_i i st1.(call_stack) [] hl' tl tl' sf1 sf1' H_split_i_st1 H_split_i_st1') as [H_l'_1 [H_tl_1 H_sf1]]. 
      pose proof (split_on_same_i i st2.(call_stack) [] hl' tl tl' sf2 sf2' H_split_i_st2 H_split_i_st2') as [H_l'_2 [H_tl_2 H_sf2]]. 
      subst hl' tl' sf1' sf2'.

      rewrite H_fname_sf1 in H_exec_func.
      rewrite H_fname_sf2 in E_st2'.

      repeat split; try reflexivity.

      * left.
        rewrite E_st2'.
        rewrite <- H_exec_func.

        destruct H_split_i_st1' as [_ [_ H_len_tl]].

        unfold equiv_states_up_to_i_v.
        simpl.
        repeat split; try assumption.
        ** rewrite H_len_tl.
           lia.
        ** exists [{|
                    Liveness_snd.StackFrameD.fname := fname;
                    Liveness_snd.StackFrameD.locals := locals';
                    Liveness_snd.StackFrameD.curr_bid := entry_bid func;
                    Liveness_snd.StackFrameD.pc := 0
                  |}].
          exists tl, sf1, sf2.  
          split.
          *** unfold split_at_i.
              repeat split.
              **** simpl.
                   rewrite H_len_tl.
                   lia.
              **** exact H_len_tl.
          *** unfold split_at_i.
              repeat split; try assumption.
              **** simpl.
                   rewrite H_len_tl.
                   lia.
      * rewrite E_st2'.
        rewrite <- H_exec_func.
        unfold equiv_vars_in_top_frame.
        simpl.
        repeat split; try reflexivity.
        intros.
        rewrite DialectFactsD.eqb_eq.
        reflexivity.
        

      + apply (live_at_error_1_snd p i fname bid b pc s st1 st2 st1' v "Failed to create initial variable assignment" H_b_exists H_live_at_pc H_equiv_st1_st2 H_exec_func H_not_In_v_s).
 
      
    (* function does exists *)
    - apply (live_at_error_1_snd p i fname bid b pc s st1 st2 st1' v "Function not found in call" H_b_exists H_live_at_pc H_equiv_st1_st2 H_exec_func H_not_In_v_s).
  Qed.


  Lemma live_at_exec_func_2_snd:
    forall (p: CFGProgD.t) (i: nat) (fname: FuncName.t) (bid: BlockID.t) (b: BlockD.t) (pc: nat) (s: VarSet.t) (instr: InstrD.t) (func_name: FuncName.t) (st1 st2 st1': StateD.t) (top_sf sf1 sf2: StackFrameD.t) (hl tl: CallStackD.t) (values: list D.value_t) (v: VarID.t),
      CFGProgD.get_block p fname bid = Some b ->
      SmallStepD.get_next_instr st1 p = Some instr ->
      live_at_pc p fname bid pc s ->
      equiv_states_up_to_i_v p i fname bid pc v st1 st2 ->
      split_at_i i st1.(call_stack) (top_sf::hl) tl sf1 ->
      split_at_i i st2.(call_stack) (top_sf::hl) tl sf2 ->
      execute_func p func_name values instr.(output) top_sf (hl++(sf1::tl)) st1 = st1' ->
      ~ VarSet.In v s ->
        exists st2' bid' pc' s',
          execute_func p func_name values instr.(output) top_sf (hl++(sf2::tl)) st2 = st2'
          /\
            equiv_states_up_to_not_live_v_or_eq_states p i fname bid' pc' s' st1' st2' v (* we reach state equivalent to st1' *)
          /\
            equiv_vars_in_top_frame p st1' st2'. (* the top frames are equivalent wrt the accessed variables *)
  Proof.
    intros p i fname bid b pc s instr func_name st1 st2 st1' top_sf sf1 sf2 hl' tl values v.
    intros H_b_exists H_get_instr H_live_at_pc H_equiv_st1_st2 H_split_i_st1 H_split_i_st2 H_exec_func H_not_In_v_s.
    unfold execute_func in H_exec_func.
    unfold execute_func.

    (* split on wether the function exists *)
    destruct (get_func p func_name) as [func|] eqn:E_get_func.
    
    (* function exists *)
    - destruct (set_all LocalsD.empty (args func) values) as [locals'|] eqn:H_set_all.

      (* set_all succeeded *)
      + remember {|
                   Liveness_snd.StateD.call_stack :=
                   {|
                      Liveness_snd.StackFrameD.fname := StackFrameD.fname top_sf;
                      Liveness_snd.StackFrameD.locals := locals';
                      Liveness_snd.StackFrameD.curr_bid := entry_bid func;
                      Liveness_snd.StackFrameD.pc := 0
                  |} :: top_sf :: hl' ++ sf2 :: tl;
                  Liveness_snd.StateD.status := status st2;
                 Liveness_snd.StateD.dialect_state := dialect_state st2
         |} as st2' eqn:E_st2'.

      exists st2', bid, pc, s.

      assert(H_equiv_st1_st2' := H_equiv_st1_st2).
      destruct H_equiv_st1_st2' as [H_lt_i [H_len_call_stack [H_status [H_dialect [hl'' [tl' [sf1' [sf2' [H_split_i_st1' [H_split_i_st2' H_equiv_sf1_sf2']]]]]]]]]].
      destruct_equiv_frames H_equiv_sf1_sf2'.

      pose proof (split_on_same_i i st1.(call_stack) (top_sf :: hl') hl'' tl tl' sf1 sf1' H_split_i_st1 H_split_i_st1') as [H_l'_1 [H_tl_1 H_sf1]]. 
      pose proof (split_on_same_i i st2.(call_stack) (top_sf :: hl') hl'' tl tl' sf2 sf2' H_split_i_st2 H_split_i_st2') as [H_l'_2 [H_tl_2 H_sf2]]. 
      subst hl'' tl' sf1' sf2'.

      repeat split; try reflexivity.

      * left.
        rewrite E_st2'.
        rewrite <- H_exec_func.

        destruct H_split_i_st1 as [_ [_ H_len_tl]].

        unfold equiv_states_up_to_i_v.
        simpl.
        repeat split; try assumption.
        ** rewrite length_app.
           simpl.             
           rewrite H_len_tl.
           lia.
        ** repeat rewrite length_app.
           simpl.    
           reflexivity.
        ** exists ({|
  Liveness_snd.StackFrameD.fname := StackFrameD.fname top_sf;
  Liveness_snd.StackFrameD.locals := locals';
  Liveness_snd.StackFrameD.curr_bid := entry_bid func;
  Liveness_snd.StackFrameD.pc := 0
|}::top_sf :: hl'), tl, sf1, sf2. 
           repeat split; try assumption.      
          repeat split; try assumption.
          *** simpl.
              rewrite length_app.
              simpl.
              rewrite H_len_tl.
              lia.
          *** simpl.
              rewrite length_app.
              simpl.
              rewrite H_len_tl.
              lia.
      * rewrite E_st2'.
        rewrite <- H_exec_func.
        unfold equiv_vars_in_top_frame.
        simpl.
        repeat split; try reflexivity.
        intros.
        rewrite DialectFactsD.eqb_eq.
        reflexivity.

      + apply (live_at_error_1_snd p i fname bid b pc s st1 st2 st1' v "Failed to create initial variable assignment" H_b_exists H_live_at_pc H_equiv_st1_st2 H_exec_func H_not_In_v_s).
 
      
    (* function does exists *)
    - apply (live_at_error_1_snd p i fname bid b pc s st1 st2 st1' v "Function not found in call" H_b_exists H_live_at_pc H_equiv_st1_st2 H_exec_func H_not_In_v_s).
  Qed.


  Lemma live_at_exec_inst_snd:   
    forall (p: CFGProgD.t) (i: nat) (fname: FuncName.t) (bid: BlockID.t) (b: BlockD.t) (pc: nat) (s: VarSet.t) (instr: InstrD.t),
      CFGProgD.get_block p fname bid = Some b ->
      live_at_pc p fname bid pc s ->
      forall  (st1 st2 st1': StateD.t) (v: VarID.t),
        equiv_states_up_to_i_v p i fname bid pc v st1 st2 ->
        SmallStepD.get_next_instr st1 p = Some instr ->
        SmallStepD.execute_instr instr st1 p = st1' ->
        ~ VarSet.In v s ->
        exists st2' bid' pc' s',
          SmallStepD.execute_instr instr st2 p = st2' (* we can make an execution *)
          /\
            equiv_states_up_to_not_live_v_or_eq_states p i fname bid' pc' s' st1' st2' v (* we reach state equivalent to st1' *)
          /\
            equiv_vars_in_top_frame p st1' st2'. (* the top frames are equivalent wrt the accessed variables *)
  Proof.
    intros p i fname bid b pc s instr H_b_exists H_live_at_pc st1 st2 st1' v H_equiv_st1_st2 H_get_instr H_exec_inst_st1 H_not_In_v_s.
    
    destruct_equiv_states H_equiv_st1_st2.
    destruct_split_i H_split_i_st1 st1.
    destruct_split_i H_split_i_st2 st2.
    destruct_equiv_frames H_equiv_sf1_sf2.
    
    unfold SmallStepD.execute_instr in H_exec_inst_st1.
    rewrite H_call_stack_st1 in H_exec_inst_st1.
    
    unfold SmallStepD.execute_instr.
    rewrite H_call_stack_st2.
    
    (* we split on wether the top frame is i-th one*)
    destruct hl as [|top_sf hl'] eqn:E_hl.

    (* the case where the top stack frame is the one with different values for v *)
    - simpl.
      simpl in H_exec_inst_st1.

      (* v is not in the input arguments *)
      assert( H_get_instr' := H_get_instr).
      unfold SmallStepD.get_next_instr in H_get_instr'.
      rewrite H_call_stack_st1 in H_get_instr'.
      simpl in H_get_instr'. 
      rewrite H_fname_sf1, H_bid_sf1, H_pc_sf1 in H_get_instr'.
      pose proof(not_live_v_not_in_input_args p fname bid b pc s instr v H_b_exists H_get_instr' H_live_at_pc H_not_In_v_s) as H_not_In_v_input.

      (* rewrite sf2 to sf1 in eval_sexpr *)
      rewrite <- (eval_sexpr_snd (instr.(input)) fname bid pc v sf1 sf2 H_equiv_sf1_sf2 H_not_In_v_input).
      remember (eval_sexpr (input instr) sf1) as values eqn:E_values.
      
      (* now we split on the opeartion *)
      destruct instr.(op) as [ f_or_op | other_instr ] eqn:E_op; try destruct f_or_op as [f_call | opcode]; try destruct other_instr.
      (* function call *)
      + apply (live_at_exec_func_1_snd p i fname bid b pc s instr f_call st1 st2 st1' sf1 sf2 tl values v H_b_exists H_get_instr H_live_at_pc H_equiv_st1_st2 H_split_i_st1 H_split_i_st2 H_exec_inst_st1 H_not_In_v_s).

      (* opcode  call *)
      + apply (live_at_exec_opcode_1_snd p i fname bid b pc s instr opcode st1 st2 st1' sf1 sf2 tl values v H_b_exists H_get_instr H_live_at_pc H_equiv_st1_st2 H_split_i_st1 H_split_i_st2 H_exec_inst_st1 H_not_In_v_s).

      (* assignment *)
      + apply (live_at_exec_assignment_1_snd p i fname bid b pc s instr st1 st2 st1' sf1 sf2 tl values v H_b_exists H_get_instr H_live_at_pc H_equiv_st1_st2 H_split_i_st1 H_split_i_st2 H_exec_inst_st1 H_not_In_v_s).




    (* the case where the top stack frame is not the one *)
    - rewrite <- app_comm_cons in H_exec_inst_st1.
      rewrite <- app_comm_cons.
      
      rewrite <- app_comm_cons in H_call_stack_st1.
      rewrite <- app_comm_cons in H_call_stack_st2.

      (* now we split on the opeartion *)
      destruct instr.(op) as [ f_or_op | other_instr ] eqn:E_op; try destruct f_or_op as [f_call | opcode]; try destruct other_instr.
     
      (* function call *)
      + remember (eval_sexpr (input instr) top_sf) as values eqn:E_values.
        apply (live_at_exec_func_2_snd p i fname bid b pc s instr f_call st1 st2 st1' top_sf sf1 sf2 hl' tl values v H_b_exists H_get_instr H_live_at_pc H_equiv_st1_st2 H_split_i_st1 H_split_i_st2 H_exec_inst_st1 H_not_In_v_s).

      (* opcode  call *)
      + remember (eval_sexpr (input instr) top_sf) as values eqn:E_values.
        apply (live_at_exec_opcode_2_snd p i fname bid b pc s instr opcode st1 st2 st1' top_sf sf1 sf2 hl' tl values v H_b_exists H_get_instr H_live_at_pc H_equiv_st1_st2 H_split_i_st1 H_split_i_st2 H_exec_inst_st1 H_not_In_v_s).

      (* assignment *)
      + remember (eval_sexpr (input instr) top_sf) as values eqn:E_values.
        apply (live_at_exec_assignment_2_snd p i fname bid b pc s instr st1 st2 st1' top_sf sf1 sf2 hl' tl values v H_b_exists H_get_instr H_live_at_pc H_equiv_st1_st2 H_split_i_st1 H_split_i_st2 H_exec_inst_st1 H_not_In_v_s).
  Qed.
        
  
(* revised up to here *)
   
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
          equiv_vars_in_top_frame p st1' st2'.
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
           (*{*)
             unfold add_jump_var_if_applicable in H_sout.
             rewrite E_b_exit_info in H_sout.
             pose proof (not_In_preserves_eq  sout (VarSet.add cond_var s) v H_sout H_not_In_v_s) as H_not_In_v_add_cvar.
             rewrite VarSet.add_spec in H_not_In_v_add_cvar.
             apply Decidable.not_or in H_not_In_v_add_cvar as [H_v_neq_cvar _].
             congruence.
           (*}.*)
           
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
                       (*{*)
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
                       (*}.*)

                       rewrite <- (eval_sexpr_snd phi_invars fname bid pc v sf1 sf2 H_equiv_sf1_sf2 H_not_In_v_input).

                       destruct (SmallStepD.VariableAssignmentD.assign_all (SmallStepD.StackFrameD.variable_assignments sf1) phi_outvars (SmallStepD.eval_sexpr phi_invars sf1)) as [var_assignments_1|] eqn:E_assign_all_1.

                       ***** pose proof (set_all_some phi_outvars (SmallStepD.eval_sexpr phi_invars sf1) (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) var_assignments_1 E_assign_all_1) as [var_assignments_2 E_assign_all_2].
                       rewrite E_assign_all_2.
                       
                       rewrite <- live_at_pc_zero_eq_live_in in H_live_at_pc_if_true.
                       apply (live_at_pc'_0_equiv_live_at_pc_0 p fname next_bid next_b s1' E_next_b) in H_live_at_pc_if_true.

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
                                     rewrite <- (set_all_preserves_eq_up_to_eq phi_outvars (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) v (SmallStepD.eval_sexpr phi_invars sf1) var_assignments_1 var_assignments_2 H_v_in_output H_equiv_assign_sf1_sf2 E_assign_all_1 E_assign_all_2) in E_st2'.
                            
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
                                                          apply (set_all_preserves_eq_up_to phi_outvars (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) v (SmallStepD.eval_sexpr phi_invars sf1) var_assignments_1 var_assignments_2 H_v_not_in_output H_equiv_assign_sf1_sf2 E_assign_all_1 E_assign_all_2).

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

                              ******* rewrite <- (set_all_preserves_eq_up_to_eq phi_outvars (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) v (SmallStepD.eval_sexpr phi_invars sf1) var_assignments_1 var_assignments_2 H_v_in_output H_equiv_assign_sf1_sf2 E_assign_all_1 E_assign_all_2) in E_st2'.
                            
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
                                     intros v0 s0 b_top H_b_top_exists H_accessed_vars H_In_v0_s0.
                                     rewrite E_next_b in H_b_top_exists. injection H_b_top_exists as H_b_top_exists. subst b_top.


                                   assert(H_not_v_In_s'': ~ VarSet.In v s1').
                                   (*{*)
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
                                   (*}.*)


                                   ******** apply (set_all_preserves_eq_up_to phi_outvars (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) v (SmallStepD.eval_sexpr phi_invars sf1) var_assignments_1 var_assignments_2 H_v_not_in_output H_equiv_assign_sf1_sf2 E_assign_all_1 E_assign_all_2).

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
                                    ******* intros v0 s0 b_top H_b_top_exists H_accessed_vars H_In_v0_s0.
                                            rewrite H_fname_sf1 in H_b_top_exists.
                                            rewrite H_bid_sf1 in H_b_top_exists.
                                            rewrite H_b_exists in H_b_top_exists. injection H_b_top_exists as H_b_top_exists. subst b_top.
                                            rewrite H_pc_sf1 in H_accessed_vars.
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
                       ***** intros v0 s0 b_top H_b_top_exists H_accessed_vars H_In_v0_s0.
                             rewrite H_fname_sf1 in H_b_top_exists.
                             rewrite H_bid_sf1 in H_b_top_exists.
                             rewrite H_b_exists in H_b_top_exists. injection H_b_top_exists as H_b_top_exists. subst b_top.
                             rewrite H_pc_sf1 in H_accessed_vars.
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
                       (*{*)
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
                       (*}.*)

                       rewrite <- (eval_sexpr_snd phi_invars fname bid pc v sf1 sf2 H_equiv_sf1_sf2 H_not_In_v_input).

                       destruct (SmallStepD.VariableAssignmentD.assign_all (SmallStepD.StackFrameD.variable_assignments sf1) phi_outvars (SmallStepD.eval_sexpr phi_invars sf1)) as [var_assignments_1|] eqn:E_assign_all_1.

                       ***** pose proof (set_all_some phi_outvars (SmallStepD.eval_sexpr phi_invars sf1) (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) var_assignments_1 E_assign_all_1) as [var_assignments_2 E_assign_all_2].
                              rewrite E_assign_all_2.
                       
                              rewrite <- live_at_pc_zero_eq_live_in in H_live_at_pc_if_false.
                              apply (live_at_pc'_0_equiv_live_at_pc_0 p fname next_bid next_b s2' E_next_b) in H_live_at_pc_if_false.

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
                                     rewrite <- (set_all_preserves_eq_up_to_eq phi_outvars (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) v (SmallStepD.eval_sexpr phi_invars sf1) var_assignments_1 var_assignments_2 H_v_in_output H_equiv_assign_sf1_sf2 E_assign_all_1 E_assign_all_2) in E_st2'.
                            
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
                                                          apply (set_all_preserves_eq_up_to phi_outvars (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) v (SmallStepD.eval_sexpr phi_invars sf1) var_assignments_1 var_assignments_2 H_v_not_in_output H_equiv_assign_sf1_sf2 E_assign_all_1 E_assign_all_2).

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

                              ******* rewrite <- (set_all_preserves_eq_up_to_eq phi_outvars (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) v (SmallStepD.eval_sexpr phi_invars sf1) var_assignments_1 var_assignments_2 H_v_in_output H_equiv_assign_sf1_sf2 E_assign_all_1 E_assign_all_2) in E_st2'.
                            
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
                                     intros v0 s0 b_top H_b_top_exists H_accessed_vars H_In_v0_s0.

                                     rewrite E_next_b in H_b_top_exists. injection H_b_top_exists as H_b_top_exists. subst b_top.


                                   assert(H_not_v_In_s'': ~ VarSet.In v s2').
                                   (*{*)
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
                                   (*}.*)


                                   ******** apply (set_all_preserves_eq_up_to phi_outvars (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) v (SmallStepD.eval_sexpr phi_invars sf1) var_assignments_1 var_assignments_2 H_v_not_in_output H_equiv_assign_sf1_sf2 E_assign_all_1 E_assign_all_2).

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
                                    ******* intros v0 s0 b_top H_b_top_exists H_accessed_vars H_In_v0_s0.

                                            rewrite H_fname_sf1 in H_b_top_exists.
                                            rewrite H_bid_sf1 in H_b_top_exists.
                                            rewrite H_b_exists in H_b_top_exists. injection H_b_top_exists as H_b_top_exists. subst b_top.
                                    
                                            rewrite H_pc_sf1 in H_accessed_vars.
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
                       ***** intros v0 s0 b_top H_b_top_exists H_accessed_vars H_In_v0_s0.

                             rewrite H_fname_sf1 in H_b_top_exists.
                             rewrite H_bid_sf1 in H_b_top_exists.
                             rewrite H_b_exists in H_b_top_exists. injection H_b_top_exists as H_b_top_exists. subst b_top.

                             rewrite H_pc_sf1 in H_accessed_vars.
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
                 (*{*)
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
                 (*}.*)

                 rewrite <- (eval_sexpr_snd phi_invars fname bid pc v sf1 sf2 H_equiv_sf1_sf2 H_not_In_v_input).

                 destruct (SmallStepD.VariableAssignmentD.assign_all (SmallStepD.StackFrameD.variable_assignments sf1) phi_outvars (SmallStepD.eval_sexpr phi_invars sf1)) as [var_assignments_1|] eqn:E_assign_all_1.

                 **** pose proof (set_all_some phi_outvars (SmallStepD.eval_sexpr phi_invars sf1) (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) var_assignments_1 E_assign_all_1) as [var_assignments_2 E_assign_all_2].
                      rewrite E_assign_all_2.

                      rewrite <- live_at_pc_zero_eq_live_in in H_live_in_next_pc.
                      apply (live_at_pc'_0_equiv_live_at_pc_0 p fname next_bid next_b s' E_next_b) in H_live_in_next_pc.
                      
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
                                   rewrite <- (set_all_preserves_eq_up_to_eq phi_outvars (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) v (SmallStepD.eval_sexpr phi_invars sf1) var_assignments_1 var_assignments_2 H_v_in_output H_equiv_assign_sf1_sf2 E_assign_all_1 E_assign_all_2) in E_st2'.
                            
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
                                                    apply (set_all_preserves_eq_up_to phi_outvars (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) v (SmallStepD.eval_sexpr phi_invars sf1) var_assignments_1 var_assignments_2 H_v_not_in_output H_equiv_assign_sf1_sf2 E_assign_all_1 E_assign_all_2).
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
                      
                            ****** rewrite <- (set_all_preserves_eq_up_to_eq phi_outvars (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) v (SmallStepD.eval_sexpr phi_invars sf1) var_assignments_1 var_assignments_2 H_v_in_output H_equiv_assign_sf1_sf2 E_assign_all_1 E_assign_all_2) in E_st2'.
                            
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
                                   intros v0 s0 b_top H_b_top_exist H_accessed_vars H_In_v0_s0.

                                   rewrite E_next_b in H_b_top_exist. injection H_b_top_exist as H_b_top_exist. subst b_top.


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


                                   apply (set_all_preserves_eq_up_to phi_outvars (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) v (SmallStepD.eval_sexpr phi_invars sf1) var_assignments_1 var_assignments_2 H_v_not_in_output H_equiv_assign_sf1_sf2 E_assign_all_1 E_assign_all_2).

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
                            ****** intros v0 s0 b_top H_b_top_exists H_accessed_vars H_In_v0_s0.
                                   rewrite H_fname_sf1 in H_b_top_exists.
                                   rewrite H_bid_sf1 in H_b_top_exists.
                                   rewrite H_b_exists in H_b_top_exists. injection H_b_top_exists as H_b_top_exists. subst b_top.
                                   rewrite H_pc_sf1 in H_accessed_vars.
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
             *** intros v0 s0 b_top H_b_top_exists H_accessed_vars H_In_v0_s0.

                 rewrite H_fname_sf1 in H_b_top_exists.
                 rewrite H_bid_sf1 in H_b_top_exists.
                 rewrite H_b_exists in H_b_top_exists. injection H_b_top_exists as H_b_top_exists. subst b_top.
                 rewrite H_pc_sf1 in H_accessed_vars.
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
             *** intros v0 s0 b_top H_b_top_exists H_accessed_vars H_In_v0_s0.
                 rewrite H_fname_sf1 in H_b_top_exists.
                 rewrite H_bid_sf1 in H_b_top_exists.
                 rewrite H_b_exists in H_b_top_exists. injection H_b_top_exists as H_b_top_exists. subst b_top.
                 rewrite H_pc_sf1 in H_accessed_vars.
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
                                            ******** intros v0 s0 b_top H_b_top_exists H_accessed_vars H_In_v0_s0.
                                                     rewrite H_fname_sf1 in H_b_top_exists.
                                                     rewrite H_bid_sf1 in H_b_top_exists.
                                                     rewrite H_b_exists in H_b_top_exists. injection H_b_top_exists as H_b_top_exists. subst b_top.
                                                     rewrite H_pc_sf1 in H_accessed_vars.

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
                      ***** intros v0 s0 b_top H_b_top_exists H_accessed_vars H_In_v0_s0.
                            rewrite H_fname_sf1 in H_b_top_exists.
                            rewrite H_bid_sf1 in H_b_top_exists.
                            rewrite H_b_exists in H_b_top_exists. injection H_b_top_exists as H_b_top_exists. subst b_top.
                            rewrite H_pc_sf1 in H_accessed_vars.
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
                 **** intros v0 s0 b_top H_b_top_exists H_accessed_vars H_In_v0_s0.
                      rewrite H_fname_sf1 in H_b_top_exists.
                      rewrite H_bid_sf1 in H_b_top_exists.
                      rewrite H_b_exists in H_b_top_exists. injection H_b_top_exists as H_b_top_exists. subst b_top.
                      rewrite H_pc_sf1 in H_accessed_vars.
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
          ** intros v0 s0 b_top H_b_top_exists H_accessed_vars H_In_v0_s0.
             rewrite H_fname_sf1 in H_b_top_exists.
             rewrite H_bid_sf1 in H_b_top_exists.
             rewrite H_b_exists in H_b_top_exists. injection H_b_top_exists as H_b_top_exists. subst b_top.
             rewrite H_pc_sf1 in H_accessed_vars.
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
                         ****** pose proof (set_all_some (SmallStepD.SmartContractD.BlockD.InstructionD.output instr)  (SmallStepD.eval_sexpr rs top_sf)  (SmallStepD.StackFrameD.variable_assignments sf1)  (SmallStepD.StackFrameD.variable_assignments sf2) prev_sf_var_assignment_1 E_prev_sf_var_assignment_1 ) as [prev_sf_var_assignment_2 E_prev_sf_var_assignment_2].
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
                                         
                                                   rewrite <- (set_all_preserves_eq_up_to_eq (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) (StackFrameD.variable_assignments sf1) (StackFrameD.variable_assignments sf2) v (SmallStepD.eval_sexpr rs top_sf) prev_sf_var_assignment_1 prev_sf_var_assignment_2 H_v_in_output H_equiv_assign_sf1_sf2  E_prev_sf_var_assignment_1 E_prev_sf_var_assignment_2) in H_st2'.
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
                                                              *********** apply (set_all_preserves_eq_up_to (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) v (SmallStepD.eval_sexpr rs top_sf) prev_sf_var_assignment_1 prev_sf_var_assignment_2 H_v_not_in_output H_equiv_assign_sf1_sf2 E_prev_sf_var_assignment_1 E_prev_sf_var_assignment_2).
                                                    ********** apply H_live_at_S_pc.
                                                    ********** apply (not_In_v_fwd v s sout instr H_sout H_not_In_v_s H_v_not_in_output).

              ******** rewrite H_st2'.
                       rewrite <- H_handle_block_finish.
                       unfold equiv_vars_in_top_frame.
                       simpl.
                       repeat split.
                       intros v0 s0 b_top H_b_top_exists H_accessed_vars H_in_v0_s0.           

                       rewrite E_next_b in H_b_top_exists. injection H_b_top_exists as H_b_top_exists. subst b_top.

                       (* wether v in output or not *)
                       pose proof (varlist_in_dec (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) v) as H_v_output.
                       destruct H_v_output as [H_v_in_output | H_v_not_in_output].

                        ********* rewrite (set_all_preserves_eq_up_to_eq (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) (StackFrameD.variable_assignments sf1) (StackFrameD.variable_assignments sf2) v (SmallStepD.eval_sexpr rs top_sf) prev_sf_var_assignment_1 prev_sf_var_assignment_2 H_v_in_output H_equiv_assign_sf1_sf2  E_prev_sf_var_assignment_1 E_prev_sf_var_assignment_2).
                                   reflexivity.
                        ********* pose proof (not_In_v_fwd v s sout instr H_sout H_not_In_v_s H_v_not_in_output) as H_not_In_v_s'.
                                  rewrite Nat.add_comm in H_accessed_vars. simpl in H_accessed_vars.

                        pose proof (accessed_var_instr_neq_v p fname bid b (S pc) s0 v0 s v E_next_b H_live_at_S_pc H_not_In_v_s' H_accessed_vars H_in_v0_s0) as H_v0_neq_v.
                               
                                  apply (set_all_preserves_eq_up_to (SmallStepD.SmartContractD.BlockD.InstructionD.output instr) (SmallStepD.StackFrameD.variable_assignments sf1) (SmallStepD.StackFrameD.variable_assignments sf2) v (SmallStepD.eval_sexpr rs top_sf) prev_sf_var_assignment_1 prev_sf_var_assignment_2 H_v_not_in_output H_equiv_assign_sf1_sf2  E_prev_sf_var_assignment_1 E_prev_sf_var_assignment_2 v0 H_v0_neq_v).

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
            equiv_vars_in_top_frame p st1' st2'.
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
            SmartContractD.get_block p fname bid' = Some b'  /\ 
            (equiv_states_up_to_i_v p i fname bid' pc' v st1' st2' \/ st2' = st1') /\
            equiv_vars_in_top_frame p st1' st2'.
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
      + apply H_b_exists.
      + left.
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
        * apply H_equiv_vars_in_top_frame_st1'_st2'.
         
      + subst st2_1_step.
        exists st1'.
        exists pc'.
        exists b'.
        exists bid'.
        repeat split.
        
        * rewrite H_st2_1_step_eq_st1_1_step.
          apply H_eval_st1.
        * apply H_exists_b'.
        * right. reflexivity.
        * apply equiv_vars_in_top_frame_refl.
  Qed.

End Liveness_snd.
