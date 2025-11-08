Require Import FORYU.state.
Require Import FORYU.program.
Require Import FORYU.semantics.
Require Import Orders.
Require Import OrdersEx.
Require Import MSets.
Require Import Arith.
Require Import List.
Import ListNotations.

Set Bullet Behavior "Strict Subproofs".

Module VarSet := Make Nat_as_OT.

Module Liveness (D: DIALECT).

  Module SmallStepD := SmallStep(D).
  Module StateD := SmallStepD.StateD.
  Module SmartContractD := SmallStepD.SmartContractD.
  Module FunctionD := SmartContractD.FunctionD.
  Module BlockD := SmartContractD.BlockD.
  Module ExitInfoD := BlockD.ExitInfoD.
  Module InstructionD := BlockD.InstructionD.
  Module YULVariableMapD := BlockD.PhiInfoD.YULVariableMapD.
  Module SimpleExprD := BlockD.PhiInfoD.YULVariableMapD.SimpleExprD.

  (* convert a list to a set *)
  Fixpoint list_to_set (l : list nat) : VarSet.t :=
    match l with
    | nil => VarSet.empty
    | x::xs => VarSet.add x (list_to_set xs)
    end.

  Fixpoint extract_yul_vars (l : list SimpleExprD.t) : list nat :=
    match l with
    | nil => nil
    | x::xs =>
        let xs_vs := extract_yul_vars xs in
        match x with
        | inl idx => idx::xs_vs
        | inr _ => xs_vs
        end
    end.

  Fixpoint apply_phi (l : YULVariableMapD.t) (s: VarSet.t) :=
    match l with
    | nil => s
    | (dest,orig)::vs =>
        match orig with
        | inl var =>
            if (VarSet.mem dest s) then
              apply_phi vs (VarSet.add var (VarSet.remove dest s))
            else
              apply_phi vs s
        | inr _ =>
            apply_phi vs s
        end
    end.


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
      
  Lemma apply_phi_preserves_equal:
    forall l s1 s2,
      VarSet.Equal s1 s2 ->
      VarSet.Equal (apply_phi l s1) (apply_phi l s2).
  Proof.
    induction l as [|a l' IHl'].
    + trivial.
    + intros s1 s2 H_s1_eq_s2.
      unfold apply_phi. fold apply_phi.
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

  Fixpoint prop_live_set_bkw (l: list InstructionD.t) (s: VarSet.t) : VarSet.t  :=
    match l with
    | nil => s
    | i::l' =>
        let s' :=  prop_live_set_bkw l' s in
        let inset := list_to_set (extract_yul_vars i.(InstructionD.input)) in
        let outset := list_to_set i.(InstructionD.output) in
        (VarSet.union (VarSet.diff s' outset) inset)
    end.

  Lemma prop_live_set_bkw_preserves_equal:
        forall l s1 s2,
          VarSet.Equal s1 s2 ->
          VarSet.Equal (prop_live_set_bkw l s1) (prop_live_set_bkw l s2).
  Proof.
    induction l as [|a l' IHl'].
    + trivial.
    + intros s1 s2 H_s1_eq_s2.
      unfold prop_live_set_bkw. fold prop_live_set_bkw.
      apply (union_preserves_equal
               (VarSet.diff (prop_live_set_bkw l' s1) (list_to_set (InstructionD.output a)))
               (VarSet.diff (prop_live_set_bkw l' s2) (list_to_set (InstructionD.output a)))
               (list_to_set (extract_yul_vars (InstructionD.input a)))
               (list_to_set (extract_yul_vars (InstructionD.input a)))
               (diff_preserves_equal (prop_live_set_bkw l' s1) (prop_live_set_bkw l' s2) (list_to_set (InstructionD.output a)) (list_to_set (InstructionD.output a)) (IHl' s1 s2 H_s1_eq_s2) (varset_equal_refl (list_to_set (InstructionD.output a))))
               (varset_equal_refl (list_to_set (extract_yul_vars (InstructionD.input a))))).
  Qed.

  Definition add_jump_var_if_applicable (b: BlockD.t) (s: VarSet.t) :=
    match b.(BlockD.exit_info) with
    | ExitInfoD.ConditionalJump cond_var _ _ => VarSet.add cond_var s
    | _ => s
      end.

  Lemma add_jump_var_if_applicable_preserves_equal:
    forall b s1 s2,
      VarSet.Equal s1 s2 ->
      VarSet.Equal (add_jump_var_if_applicable b s1) (add_jump_var_if_applicable b s2).
  Proof.
    intros b s1 s2 H_s1_eq_s2.
    unfold add_jump_var_if_applicable.
    destruct (BlockD.exit_info b); try apply H_s1_eq_s2.
    rewrite (add_preserves_equal s1 s2 cond_var H_s1_eq_s2).
    apply varset_equal_refl.
    Qed.
  
  
  (*
    Th  e following co-inductive defintions is for live variable properties.
    
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
    VarSet.Equal sout (apply_phi (BlockD.phi_function next_b bid) s) ->
    live_out p fname bid sout  (* sout is the set of live variable at the exit of p/fname/bid *)

  (* A block with a conditional jump *)
  | lo_block_w_cond_jump (fname : FunctionName.t) (bid next_bid_if_true next_bid_if_false:  BlockID.t) (cond_var: nat) (b next_b_if_true next_b_if_false: BlockD.t) (s1 s2 sout: VarSet.t):
    SmartContractD.get_block p fname bid = Some b -> (* the block exists *)
    BlockD.is_cond_jump_block b = Some (cond_var, next_bid_if_true, next_bid_if_false) -> (* the block ends with a conditional jump, and next_bid_if_true and next_bid_if_false are the identifiers of the next blocks *)
    live_in p fname next_bid_if_true s1 ->  (* s1 is the set of live at the entry of p/fname/next_bid_if_true *)
    live_in p fname next_bid_if_false s2 -> (* s2 is the set of live variables at the entry of p/fname/next_bid_if_false *)
    SmartContractD.get_block p fname next_bid_if_true = Some next_b_if_true -> (* next_b_if_true is the block with id next_bid_if_true *)
    SmartContractD.get_block p fname next_bid_if_false = Some next_b_if_false -> (* next_b_if_false is the block with id next_bid_if_false *)
    VarSet.Equal sout (VarSet.union (apply_phi (BlockD.phi_function next_b_if_true bid) s1) (apply_phi (BlockD.phi_function next_b_if_false bid) s2)) ->
    live_out p fname bid sout
  with
    live_in (p : SmartContractD.t) : FunctionName.t -> BlockID.t -> VarSet.t -> Prop :=
  | li_block_any (fname : FunctionName.t) (bid :  BlockID.t) (b: BlockD.t) (s sout: VarSet.t):
    SmartContractD.get_block p fname bid = Some b -> (* the block exists *)
    live_out p fname bid s -> (* s is the set of live variables at the exit of p/fname/bid *)
    VarSet.Equal sout (prop_live_set_bkw b.(BlockD.instructions) (add_jump_var_if_applicable b s)) ->
    live_in p fname bid sout.

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

    + apply (@lo_block_w_jump p fname bid next_bid b next_b s s2 e e0 l e1 (varset_equal_trans s2 sout (apply_phi (BlockD.phi_function next_b bid) s) (varset_equal_sym sout s2 H_s1_eq_s2) e2)).

    + apply (@lo_block_w_cond_jump p fname bid next_bid_if_true next_bid_if_false cond_var b next_b_if_true next_b_if_false s1 s0 s2 e e0 l l0 e1 e2 (varset_equal_trans s2 sout (VarSet.union (apply_phi (BlockD.phi_function next_b_if_true bid) s1) (apply_phi (BlockD.phi_function next_b_if_false bid) s0)) (varset_equal_sym sout s2 H_s1_eq_s2) e3)).
  Qed.
  
  (* The following types are used to define the result of a live-variable analysis *)
  Definition block_live_info_t := nat -> option VarSet.t.
  Definition fun_live_info_t := BlockID.t -> option (VarSet.t * VarSet.t).
  Definition sc_live_info_t := FunctionName.t -> option fun_live_info_t.


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
              VarSet.Equal b_out_info (apply_phi (BlockD.phi_function next_b b.(BlockD.bid)) next_b_in_info)
        | ExitInfoD.ConditionalJump cond_var next_bid_if_true next_bid_if_false => 
            exists next_b_if_true next_b_ift_in_info next_b_ift_out_info next_b_if_false next_b_iff_in_info next_b_iff_out_info,
            SmartContractD.get_block p f next_bid_if_true = Some next_b_if_true /\ 
            SmartContractD.get_block p f next_bid_if_false = Some next_b_if_false /\ 
              f_info next_bid_if_true = Some (next_b_ift_in_info,next_b_ift_out_info) /\
              f_info next_bid_if_false = Some (next_b_iff_in_info,next_b_iff_out_info) /\
              VarSet.Equal b_out_info (VarSet.union
                                         (apply_phi (BlockD.phi_function next_b_if_true b.(BlockD.bid)) next_b_ift_in_info)
                                         (apply_phi (BlockD.phi_function next_b_if_false b.(BlockD.bid)) next_b_iff_in_info))
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
    forall f bid b,
      SmartContractD.get_block p f bid = Some b -> (* if the block exists *)
      snd_block_info p r f b. (* it has sound information *)


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
      rewrite <- H_b_out_info_info' in H_b_in_info'.

      apply (@li_block_any p f bid b b_out_info' b_in_info' H_b_exists).

      apply (build_live_out p f bid b r f_info' b_in_info' b_out_info' H_snd_info H_b_exists H_r_f  H_f_info').
      
      rewrite <- H_b_out_info_info'.
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
    
  Definition check_live_in (r: sc_live_info_t) (f: FunctionName.t) (b: BlockD.t) : bool :=
    match (r f) with
    | None => false
    | Some f_info =>
      match f_info b.(BlockD.bid) with
      | None => false
      | Some (b_in_info,b_out_info) =>
          VarSet.equal b_in_info (prop_live_set_bkw b.(BlockD.instructions) (add_jump_var_if_applicable b b_out_info))
      end
    end.

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

  Definition check_live_out (p: SmartContractD.t) (r: sc_live_info_t) (f: FunctionName.t) (b: BlockD.t) : bool :=
    match (r f) with
    | None => false
    | Some f_info =>
        match (f_info b.(BlockD.bid)) with
        | None => false
        | Some (b_in_info,b_out_info) =>
            match b.(BlockD.exit_info) with
            | ExitInfoD.Terminated =>
                VarSet.equal b_out_info VarSet.empty 
            | ExitInfoD.ReturnBlock rs => 
                VarSet.equal b_out_info (list_to_set (extract_yul_vars rs))
            | ExitInfoD.Jump next_bid =>
                match (SmartContractD.get_block p f next_bid) with
                | None => false
                | Some next_b =>
                    match (f_info next_bid) with
                    | None => false
                    | Some (next_b_in_info,next_b_out_info) =>
                        VarSet.equal b_out_info (apply_phi (BlockD.phi_function next_b b.(BlockD.bid)) next_b_in_info)
                    end
                end
            | ExitInfoD.ConditionalJump cond_var next_bid_if_true next_bid_if_false =>
                match (SmartContractD.get_block p f next_bid_if_true) with
                | None => false
                | Some next_b_if_true =>
                    match (SmartContractD.get_block p f next_bid_if_false) with
                    | None => false
                    | Some next_b_if_false =>
                        match (f_info next_bid_if_true) with
                        | None => false
                        | Some (next_b_ift_in_info,next_b_ift_out_info) =>
                            match (f_info next_bid_if_false) with
                            | None => false
                            | Some (next_b_iff_in_info,next_b_iff_out_info) =>
                                VarSet.equal b_out_info (VarSet.union
                                                           (apply_phi (BlockD.phi_function next_b_if_true b.(BlockD.bid)) next_b_ift_in_info)
                                                           (apply_phi (BlockD.phi_function next_b_if_false b.(BlockD.bid)) next_b_iff_in_info))
                            end
                        end
                    end
                end
            end
        end
    end.

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

  Definition check_live (p: SmartContractD.t) (r: sc_live_info_t) (f: FunctionName.t) (b: BlockD.t) : bool :=
    if (check_live_in r f b) then check_live_out p r f b else false.

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
      
  Definition get_all_blocks (p: SmartContractD.t) :=
    fold_right (fun f accm => (map (fun (b: BlockD.t) => (f.(FunctionD.name),b)) f.(FunctionD.blocks))++accm) nil p.(SmartContractD.functions).
  
  Lemma get_all_blocks_correct:
    forall p l,
      get_all_blocks p = l ->
      forall fname b, In (fname,b) l <-> SmartContractD.get_block p fname b.(BlockD.bid) = Some b.
  Admitted.
  
  Fixpoint forallb_stop {A : Type} (test : A -> bool) (l : list A) : bool :=
    match l with
    | [] => true
    | x :: xs => if test x then forallb_stop test xs else false
    end.
  
  Lemma forallb_stop_if:
    forall (A: Type)  (P: A -> Prop ) (l: list A) (f: A->bool),
      (forall x, ((f x) = true -> P x)) ->
      (forallb_stop f l) = true ->
      forall a, In a l -> P a.
  Proof.
    intros A P.
    induction l as [| z l' IHl'].
    + intros.
      destruct H1.
    + intros f H H_forallbs.
      simpl in H_forallbs.
      destruct (f z) eqn:E_f_z; try discriminate.
      pose proof (H z E_f_z) as H_P_z.
      intro a.
      simpl.
      intros H_disj.
      destruct H_disj as [H_l | H_r].
    - rewrite H_l in H_P_z.
      apply H_P_z.
    - apply (IHl' f H H_forallbs a H_r).
  Qed.
  
  Lemma forallb_stop_fi:
    forall (A: Type)  (P: A -> Prop ) (f: A->bool) (l: list A) ,
      (forall a, In a l -> P a) ->
      (forall a, (P a -> (f a) = true)) ->
      (forallb_stop f l) = true.
  Proof.
    intros A P f.
    induction l as [| z l' IHl'].
    - reflexivity.
    - intro H_P_a.
      intro H_P_a_f_a.
      simpl.
      destruct (f z) eqn:E_f_z.      
      + simpl in H_P_a.
        assert (H_l': forall a : A, In a l' -> P a). intuition.
        apply (IHl' H_l'  H_P_a_f_a).
      + pose proof (H_P_a z (in_eq z l')) as H_P_z.
        pose proof (H_P_a_f_a z H_P_z) as H_f_z_false.
        rewrite H_f_z_false in E_f_z.
        discriminate E_f_z.
  Qed.
  
  Definition check_live_all_functions (p: SmartContractD.t) (r: sc_live_info_t) : bool :=
    forallb_stop (fun i => check_live p r (fst i) (snd i)) (get_all_blocks p).
  
  Lemma aux:
    forall p r i,
      (check_live p r (fst i) (snd i) = true -> snd_block_info p r (fst i) (snd i)).
  Proof.
    intros p r i.
    destruct i as [f b].
    simpl.
    apply (check_live_snd p r f b).
  Qed.
  
  Lemma aux_aux:
    forall p r i,
      (snd_block_info p r (fst i) (snd i) -> check_live p r (fst i) (snd i) = true).
  Proof.
    intros p r i.
    destruct i as [f b].
    simpl.
    apply (check_live_complete p r f b).
  Qed.
  
  Lemma check_live_function_snd:
    forall p r,
      check_live_all_functions p r = true ->
      snd_all_blocks_info p r.
  Proof.
    intros p r H_chk.
    unfold check_live_all_functions in H_chk.
    
    pose proof (forallb_stop_if
                  (FunctionName.t*BlockD.t)
                  (fun i => snd_block_info p r (fst i) (snd i))
                  (get_all_blocks p)
                  (fun i => check_live p r (fst i) (snd i))
                  (aux p r)
                  H_chk).
    
    pose proof (get_all_blocks_correct p (get_all_blocks p) eq_refl).
    
    assert(H1: forall (fname : FunctionName.t) (b : BlockD.t),
              SmartContractD.get_block p fname (BlockD.bid b) = Some b -> snd_block_info p r fname b).
      (*{*)
      intros fname b.
      pose proof (H0 fname b).
      pose proof (H (fname,b)).
      rewrite H1 in H2.
      simpl in H2.
      apply H2.
      (*}*)
    
    assert(H2: forall (fname : FunctionName.t) (b : BlockD.t) (bid: BlockID.t),
              SmartContractD.get_block p fname bid = Some b -> snd_block_info p r fname b).
      (*{*)
      intros fname b bid H_exists.
      pose proof (bid_b p fname bid b H_exists).
      rewrite <- H2 in H_exists.
      apply (H1 fname b H_exists).
      (*}*)
    
    unfold snd_all_blocks_info.
    intros f bid b.
    apply (H2 f b bid).
  Qed.


  Lemma check_live_function_complete:
    forall p r,
      snd_all_blocks_info p r -> check_live_all_functions p r = true.
  Proof.    
    intros p r H_snd.
    unfold snd_all_blocks_info in H_snd.
    
    pose proof (get_all_blocks_correct p (get_all_blocks p) eq_refl).
 
    assert( forall a,
              In a (get_all_blocks p) -> snd_block_info p r (fst a) (snd a)).
    (*{*)
      intros a.
      pose proof (H (fst a) (snd a)).
      rewrite <- surjective_pairing in H0.
      rewrite H0.
      pose proof (H_snd (fst a) (snd a).(BlockD.bid) (snd a)).
      apply H1.
    (*}*)

      
    assert ((forall a : FunctionName.t * BlockD.t,
     (fun i : FunctionName.t * BlockD.t => snd_block_info p r (fst i) (snd i)) a ->
     (fun i : FunctionName.t * BlockD.t => check_live p r (fst i) (snd i)) a = true)).
    (*{*)
      intro a.
      pose proof (check_live_complete p r (fst a) (snd a)).
      apply H1.
    (*}*)

    
    pose proof (forallb_stop_fi
                  (FunctionName.t*BlockD.t)
                  (fun i => snd_block_info p r (fst i) (snd i))
                  (fun i => check_live p r (fst i) (snd i))
                  (get_all_blocks p)
                  H0
                  (aux_aux p r)).
    
    unfold check_live_all_functions.
    apply H2.
  Qed.

  Lemma check_live_function_correct:
    forall p r,
      snd_all_blocks_info p r <-> check_live_all_functions p r = true.
  Proof.
    intros p r.
    split.
    - apply check_live_function_complete.
    - apply check_live_function_snd.
  Qed.

End Liveness.





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
