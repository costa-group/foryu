Require Import FORYU.state.
Require Import FORYU.program.
Require Import FORYU.semantics.
Require Import FORYU.liveness.
Require Import FORYU.liveness_snd.

From Stdlib Require Orders.
From Stdlib Require OrdersEx.
From Stdlib Require MSets.
From Stdlib Require Arith.
From Stdlib Require List.
Import ListNotations.
From Stdlib Require Import Relations.Relation_Operators.
Require Import stdpp.prelude.
Require Import stdpp.relations.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.Classical_Pred_Type.
From Stdlib Require Lia.


(*
  Correctness of the liveness checkers (liveness.v): the conditions
  that the liveness results must satisfy (with equations and with
  inclusions), the soundness and completeness of the checkers wrt.
  these conditions, and the link between these conditions and the
  coinductive live_in/live_out of liveness_snd.v, which are used
  there to prove the semantic property (dead variables).
*)
Module Liveness_checker_snd (D: DIALECT).

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
              VarSet.Equal b_out_info (apply_inv_phi (fst next_b.(phi_function)) (snd next_b.(phi_function) b.(bid)) next_b_in_info)
        | ExitInfoD.ConditionalJump cond_var next_bid_if_true next_bid_if_false => 
            exists next_b_if_true next_b_ift_in_info next_b_ift_out_info next_b_if_false next_b_iff_in_info next_b_iff_out_info,
            CFGProgD.get_block p fname next_bid_if_true = Some next_b_if_true /\ 
            CFGProgD.get_block p fname next_bid_if_false = Some next_b_if_false /\ 
              f_info next_bid_if_true = Some (next_b_ift_in_info,next_b_ift_out_info) /\
              f_info next_bid_if_false = Some (next_b_iff_in_info,next_b_iff_out_info) /\
              VarSet.Equal b_out_info (VarSet.union
                                         (apply_inv_phi (fst next_b_if_true.(phi_function)) (snd next_b_if_true.(phi_function) b.(bid)) next_b_ift_in_info)
                                         (apply_inv_phi (fst next_b_if_false.(phi_function)) (snd next_b_if_false.(phi_function) b.(bid)) next_b_iff_in_info))
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


  Definition snd_block_out_info_sub (p : CFGProgD.t) (r: prog_live_info_t) (fname: FuncName.t) (b: BlockD.t) : Prop :=
    exists f_info b_in_info b_out_info,
      (r fname) = Some f_info /\ (* The live-variable information of the function exists *)
        f_info b.(bid) = Some (b_in_info,b_out_info) /\ (* The live-variable information of the block exists *)
        match b.(exit_info) with
        | ExitInfoD.Terminate =>
            VarSet_Sup b_out_info  VarSet.empty 
        | ExitInfoD.ReturnBlock rs => 
            VarSet_Sup b_out_info (list_to_set (extract_yul_vars rs))
        | ExitInfoD.Jump next_bid =>
            exists next_b next_b_in_info next_b_out_info,
            CFGProgD.get_block p fname next_bid = Some next_b /\ 
              f_info next_bid = Some (next_b_in_info,next_b_out_info) /\
              VarSet_Sup b_out_info (apply_inv_phi (fst next_b.(phi_function)) (snd next_b.(phi_function) b.(bid)) next_b_in_info)
        | ExitInfoD.ConditionalJump cond_var next_bid_if_true next_bid_if_false => 
            exists next_b_if_true next_b_ift_in_info next_b_ift_out_info next_b_if_false next_b_iff_in_info next_b_iff_out_info,
            CFGProgD.get_block p fname next_bid_if_true = Some next_b_if_true /\ 
            CFGProgD.get_block p fname next_bid_if_false = Some next_b_if_false /\ 
              f_info next_bid_if_true = Some (next_b_ift_in_info,next_b_ift_out_info) /\
              f_info next_bid_if_false = Some (next_b_iff_in_info,next_b_iff_out_info) /\
              VarSet_Sup b_out_info (VarSet.union
                                         (apply_inv_phi (fst next_b_if_true.(phi_function)) (snd next_b_if_true.(phi_function) b.(bid)) next_b_ift_in_info)
                                         (apply_inv_phi (fst next_b_if_false.(phi_function)) (snd next_b_if_false.(phi_function) b.(bid)) next_b_iff_in_info))
        end.
 
  Definition snd_block_in_info_sub (r: prog_live_info_t) (fname: FuncName.t) (b: BlockD.t) : Prop :=
    exists f_info b_in_info b_out_info,
      (r fname) = Some f_info /\ (* The live-variable information of the function exists *)
        f_info b.(bid) = Some (b_in_info,b_out_info) /\ (* The live-variable information of the block exists *)
        VarSet_Sup b_in_info (prop_live_set_bkw b.(instructions) (add_jump_var_if_applicable b b_out_info)).
  
  Definition snd_block_info_sub (p: CFGProgD.t) (r: prog_live_info_t) (f: FuncName.t) (b: BlockD.t)
    : Prop :=
    snd_block_in_info_sub r f b /\ snd_block_out_info_sub p r f b.

  Definition snd_all_blocks_info_sub (p : CFGProgD.t) (r: prog_live_info_t) : Prop :=
    forall fname bid b,
      CFGProgD.get_block p fname bid = Some b -> (* if the block exists *)
      snd_block_info_sub p r fname b. (* it has sound information *)



  (* The [_sub] versions above accept over-approximations: each
     equation is replaced by an inclusion (VarSet_Sup). Exact solutions
     are a special case. *)
  Lemma snd_all_blocks_info_imp_sub:
    forall p r, snd_all_blocks_info p r -> snd_all_blocks_info_sub p r.
  Proof.
    intros p r H fname bid b H_b.
    destruct (H fname bid b H_b) as [H_in H_out].
    split.
    - destruct H_in as [f_info [b_in [b_out [H1 [H2 H3]]]]].
      exists f_info, b_in, b_out. repeat split; try assumption.
      apply varset_eq_imp_sup. exact H3.
    - destruct H_out as [f_info [b_in [b_out [H1 [H2 H3]]]]].
      exists f_info, b_in, b_out. repeat split; try assumption.
      destruct (exit_info b).
      + destruct H3 as [nt [nti [nto [nf [nfi [nfo [A [B [C [D E]]]]]]]]]].
        exists nt, nti, nto, nf, nfi, nfo. repeat split; try assumption.
        apply varset_eq_imp_sup. exact E.
      + destruct H3 as [nb [nbi [nbo [A [B C]]]]].
        exists nb, nbi, nbo. repeat split; try assumption.
        apply varset_eq_imp_sup. exact C.
      + apply varset_eq_imp_sup. exact H3.
      + apply varset_eq_imp_sup. exact H3.
  Qed.

  CoFixpoint build_live_in (p : CFGProgD.t) (fname: FuncName.t) (bid: BlockID.t) (b: BlockD.t)
    (r: prog_live_info_t) (f_info: func_live_info_t) (b_in_info b_out_info: VarSet.t)
    (H_snd_info: snd_all_blocks_info_sub p r) (H_b_exists: CFGProgD.get_block p fname bid = Some b)
    (H_f_info: (r fname) = Some f_info) (H_b_info: f_info bid = Some (b_in_info,b_out_info)) : live_in p fname bid b_in_info
  with build_live_out (p : CFGProgD.t) (fname: FuncName.t) (bid: BlockID.t) (b: BlockD.t)
         (r: prog_live_info_t) (f_info: func_live_info_t) (b_in_info b_out_info: VarSet.t)
                           (H_snd_info: snd_all_blocks_info_sub p r) (H_b_exists: CFGProgD.get_block p fname bid = Some b)
                           (H_f_info: (r fname) = Some f_info) (H_b_info: f_info bid = Some (b_in_info,b_out_info)) : live_out p fname bid b_out_info.
  Proof.
    (* the case of live_in p fname bid b_in_info *)
    - unfold snd_all_blocks_info_sub in H_snd_info.
      pose proof (H_snd_info fname bid b H_b_exists) as H_snd_b_info.
      unfold snd_block_info_sub in H_snd_b_info.
      destruct H_snd_b_info as [H_snd_b_in_info H_snd_b_out_info].
      unfold snd_block_in_info_sub in H_snd_b_in_info.
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
      unfold snd_block_info_sub in H_snd_b_info.
      destruct H_snd_b_info as [H_snd_b_in_info H_snd_b_out_info].
      unfold snd_block_out_info_sub in H_snd_b_out_info.
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

  Lemma snd_all_blocks_info_to_bid_info_sub:
    forall (p : CFGProgD.t) (r: prog_live_info_t),
      snd_all_blocks_info_sub p r ->  
      forall fname bid b,
        CFGProgD.get_block p fname bid = Some b ->
        exists f_info b_in_info b_out_info,
          (r fname) = Some f_info /\
            f_info bid = Some (b_in_info,b_out_info).
  Proof.
    intros p r H_snd_info fname bid b H_b_exists.
    pose proof (H_snd_info fname bid b H_b_exists) as H_b_info_snd.
    unfold snd_block_info_sub in H_b_info_snd.
    destruct H_b_info_snd as [H_b_in_info_snd _].
    unfold snd_block_in_info_sub in H_b_in_info_snd.
    rewrite (bid_b p fname bid b H_b_exists) in H_b_in_info_snd.
    destruct H_b_in_info_snd as [f_info [b_in_info [b_out_info [H_r_f [H_f_info _]]]]].
    exists f_info, b_in_info, b_out_info.
    split; assumption.
  Qed.
  
  Lemma snd_info_sub:
    forall (p : CFGProgD.t) (r: prog_live_info_t),
      snd_all_blocks_info_sub p r ->  
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
    unfold snd_block_info_sub in  H_b_info_snd.
    destruct H_b_info_snd as [H_b_in_info_snd H_b_out_info_snd].
    pose proof (snd_all_blocks_info_to_bid_info_sub p r H_snd_info fname bid b H_b_exists) as H_snd_all_blocks_info_to_bid_info.
    destruct H_snd_all_blocks_info_to_bid_info as [f_info [b_in_info [b_out_info [H_r_f H_f_info]]]].
    exists f_info, b_in_info, b_out_info.
    repeat split.
    - assumption.
    - assumption.
    - apply (build_live_in p fname bid b r f_info b_in_info b_out_info H_snd_info H_b_exists H_r_f H_f_info).
    - apply (build_live_out p fname bid b r f_info b_in_info b_out_info H_snd_info H_b_exists H_r_f H_f_info).
  Qed.

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
    intros p r H_snd_info.
    apply snd_info_sub.
    apply snd_all_blocks_info_imp_sub.
    exact H_snd_info.
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
  Lemma check_valid_prog_correct:
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



  (* Correctness of the subset version of the checker
     ([check_program_subset]) wrt. the [_sub] versions of the
     conditions, which use VarSet_Sup instead of VarSet.Equal. *)

  Lemma check_live_in_snd_subset:
    forall r fname b,
      check_live_in_subset r fname b = true -> snd_block_in_info_sub r fname b.
  Proof.
    intros r fname b H_check_live_in.
    unfold check_live_in_subset in H_check_live_in.
    destruct (r fname) as [f_info|] eqn:E_r_f; try discriminate.
    destruct (f_info (BlockD.bid b)) as [b_info|] eqn:E_f_info_b; try discriminate.
    destruct b_info as [b_in_info b_out_info].
    unfold snd_block_in_info_sub.
    exists f_info, b_in_info, b_out_info.
    split; try assumption.
    split; try assumption.
    unfold VarSet_Sup. rewrite <- VarSet.subset_spec.
    apply H_check_live_in.
  Qed.

  Lemma check_live_in_complete_subset:
    forall r fname b,
      snd_block_in_info_sub r fname b -> check_live_in_subset r fname b = true.
  Proof.
    intros r fname b H_snd.
    unfold snd_block_in_info_sub in H_snd.
    destruct H_snd as [f_info [b_in_info [b_out_info [H_r_f [H_f_info H_eq]]]]].
    unfold check_live_in_subset.
    destruct (r fname) as [f_info'|]; try discriminate.
    injection H_r_f as H_f_info_info'.
    rewrite H_f_info_info'.
    rewrite H_f_info.
    rewrite VarSet.subset_spec.
    apply H_eq.
  Qed.

  Lemma check_live_in_correct_subset:
    forall r fname b,
      snd_block_in_info_sub r fname b <-> check_live_in_subset r fname b = true.
  Proof.
    intros r fname b.
    split.
    + apply check_live_in_complete_subset.
    + apply check_live_in_snd_subset.
  Qed.


  Lemma check_live_out_snd_subset:
    forall p r fname b,
      check_live_out_subset p r fname b = true -> snd_block_out_info_sub p r fname b.
  Proof.
    intros p r fname b H_check_live_out.
    unfold check_live_out_subset in H_check_live_out.
    destruct (r fname) as [f_info|] eqn:E_r_f; try discriminate.
    destruct (f_info (BlockD.bid b)) as [b_info|] eqn:E_f_info_b; try discriminate.
    destruct b_info as [b_in_info b_out_info].
    unfold snd_block_out_info_sub.
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
      unfold VarSet_Sup. rewrite <- VarSet.subset_spec.
      apply H_check_live_out.

    + destruct (CFGProgD.get_block p fname next_bid) as [next_b|]; try discriminate.
      destruct (f_info next_bid) as [next_bid_info|]; try discriminate.
      destruct next_bid_info as [next_b_in_info next_b_out_info].
      exists next_b, next_b_in_info, next_b_out_info.
      split; try reflexivity.
      split; try reflexivity.
      unfold VarSet_Sup. rewrite <- VarSet.subset_spec.
      apply H_check_live_out.

    + unfold VarSet_Sup. rewrite <- VarSet.subset_spec.
      apply H_check_live_out.

    + unfold VarSet_Sup. rewrite <- VarSet.subset_spec.
      apply H_check_live_out.
  Qed.
  
Lemma check_live_out_complete_subset:
    forall p r fname b,
      snd_block_out_info_sub p r fname b -> check_live_out_subset p r fname b = true.
  Proof.
    intros p r f b H_snd.
    unfold snd_block_out_info_sub in H_snd.
    destruct H_snd as [f_info [b_in_info [b_out_info [H_r_f [H_f_info H_eq]]]]].
    unfold check_live_out_subset.
    rewrite H_r_f.
    rewrite H_f_info.

    destruct b.(exit_info) as [cond_var bid_if_true bid_if_false|next_bid|rs|] eqn:E_b_exit_info.

    + destruct H_eq as [next_b_if_true [next_b_ift_in_info [next_b_ift_out_info [next_b_if_false [next_b_iff_in_info [next_b_iff_out_info [H_b_true_exists [H_b_false_exists [if_true_info [if_false_info H_eq]]]]]]]]]].

      rewrite H_b_true_exists.
      rewrite H_b_false_exists.
      rewrite if_true_info.
      rewrite if_false_info.
      rewrite VarSet.subset_spec.
      apply H_eq.

    + destruct H_eq as [next_b [next_b_in_info [next_b_out_info [H_b_next_exists [H_next_b_f_info' H_eq]]]]].
      rewrite H_b_next_exists.
      rewrite H_next_b_f_info'.
      rewrite VarSet.subset_spec.
      apply H_eq.

    + rewrite VarSet.subset_spec.
      apply H_eq.
    + rewrite VarSet.subset_spec.
      apply H_eq.
  Qed.
  
  Lemma check_live_out_correct_subset:
    forall p r fname b,
      snd_block_out_info_sub p r fname b <-> check_live_out_subset p r fname b = true.
  Proof.
    intros p r fname b.
    split.
    + apply check_live_out_complete_subset.
    + apply check_live_out_snd_subset.
  Qed.

  Lemma check_live_snd_subset:
    forall p r fname b,
      check_live_subset p r fname b = true -> snd_block_info_sub p r fname b.
  Proof.
    intros p r fname b H_check_live.
    unfold check_live_subset in H_check_live.
    destruct (check_live_in_subset r fname b) eqn:E_check_live; try discriminate.
    unfold snd_block_info_sub.
    split.
    + apply (check_live_in_snd_subset r fname b E_check_live).
    + apply (check_live_out_snd_subset p r fname b H_check_live).
  Qed.

  Lemma check_live_complete_subset:
    forall p r fname b,
      snd_block_info_sub p r fname b -> check_live_subset p r fname b = true.
  Proof.
    intros p r fname b H_snd.
    unfold snd_block_info_sub in H_snd.
    destruct H_snd as [H_snd_in H_snd_out].
    unfold check_live_subset.
    rewrite (check_live_in_complete_subset r fname b H_snd_in).
    rewrite (check_live_out_complete_subset p r fname b H_snd_out).
    reflexivity.
  Qed.

  Lemma check_live_correct_subset:
    forall p r fname b,
      snd_block_info_sub p r fname b <-> check_live_subset p r fname b = true.
  Proof.
    intros p r fname b.
    split.
    + apply check_live_complete_subset.
    + apply check_live_snd_subset.
  Qed.

  Lemma check_blocks_snd_subset:
    forall bs fname p r,
      check_blocks_subset bs fname p r = true ->
      forall b,
        In b bs -> snd_block_info_sub p r fname b.
  Proof.
    induction bs as [|b bs' IHbs'].
    - simpl. intros fname p r H_chk b H_False.
      destruct H_False.
    - intros fname p r H_chk b0 H_in_b0_bbs'.
      simpl check_blocks_subset in H_chk.
      destruct (check_live_subset p r fname b) eqn:E_check_live; try discriminate.
      simpl in H_in_b0_bbs'.
      destruct H_in_b0_bbs' as [H_b_eq_b0 | H_in_b0_bs'].

      + subst b0.
        apply (check_live_snd_subset p r fname b E_check_live).
      + apply (IHbs' fname p r H_chk b0 H_in_b0_bs').
  Qed.

  (* If a [P e] holds for all [e] in a list, then it holds fro all elements in the tail *)
  Lemma in_cons_if_prop_subset:
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

  Lemma check_blocks_complete_subset:
    forall bs fname p r,
      (forall b, In b bs -> snd_block_info_sub p r fname b) ->
      check_blocks_subset bs fname p r = true.
  Proof.
    induction bs as [|b bs' IHbs'].    
    - simpl. intros fname p r H_snd.
      reflexivity.
    - intros fname p r H_snd.
      pose proof (H_snd b (in_eq b bs')) as H_snd_b.
      simpl.
      destruct (check_live_subset p r fname b) eqn:E_check_live.
      + apply (IHbs' fname p r (@in_cons_if_prop_subset BlockD.t b bs' (fun b => snd_block_info_sub p r fname b) H_snd)).
      + rewrite (check_live_complete_subset p r fname b H_snd_b) in E_check_live.
        discriminate E_check_live.
  Qed.
  
  Lemma check_blocks_correct_subset:
    forall bs fname p r,
      (forall b, In b bs -> snd_block_info_sub p r fname b) <->
          check_blocks_subset bs fname p r = true.
  Proof.
    intros bs fname p r.
    split.
    - apply (check_blocks_complete_subset bs fname p r).
    - apply (check_blocks_snd_subset bs fname p r).
  Qed.

  Lemma check_functions_snd_subset:
    forall fs p r,
    check_functions_subset fs p r = true ->
      forall f,
        In f fs -> forall b, In b f.(blocks) -> snd_block_info_sub p r f.(name) b.
  Proof.
    induction fs as [|f fs' IHfs'].
    - simpl.
      intros p r H_check_functions f H_False.
      destruct H_False.
    - intros p r H_check_functions f0 H_in_f0_ffs' b H_in_b_blocks_f0.
      simpl in H_in_f0_ffs'.
      destruct H_in_f0_ffs' as [H_f_eq_f0 | H_in_f0_fs'].
      + subst f0.
        simpl check_functions_subset in H_check_functions.
        destruct (check_blocks_subset f.(blocks) f.(name) p r) eqn:E_check_f; try discriminate.
        apply (check_blocks_snd_subset f.(blocks) f.(name) p r E_check_f b H_in_b_blocks_f0).
      + simpl in H_check_functions.
        destruct (check_blocks_subset f.(blocks) f.(name)); try discriminate.
        apply (IHfs' p r H_check_functions f0 H_in_f0_fs' b H_in_b_blocks_f0).
  Qed.

  
  Lemma check_functions_complete_subset:
    forall fs p r,
      (forall f, 
          In f fs -> forall b, In b f.(blocks) -> snd_block_info_sub p r f.(name) b) ->
      check_functions_subset fs p r = true.
  Proof.
    induction fs as [|f fs' IHfs'].
    - simpl.
      intros p r H_snd.
      reflexivity.
    - intros p r H_snd.
      pose proof (H_snd f) as  H_snd_f.
      simpl.
      destruct (check_blocks_subset f.(blocks) f.(name) p r) eqn:E_check_f_blocks.
      + apply IHfs'.
        intros f0 H_in_f0_fs' b.
        apply (H_snd f0 (in_cons f f0 fs' H_in_f0_fs') b).
      + rewrite (check_blocks_complete_subset f.(blocks) f.(name) p r (H_snd_f (in_eq f fs'))) in E_check_f_blocks.
        discriminate E_check_f_blocks.
  Qed.
  
  Lemma check_program_snd_subset:
    forall p r,
    check_program_subset p r = true ->
    forall f,
        In f p.(functions) -> forall b, In b f.(blocks) -> snd_block_info_sub p r f.(name) b.
  Proof.
    intros p r H_check_sc.
    intros f H_in_f_pfs b H_b_in_bsf.
    unfold check_program_subset in H_check_sc.
    apply (check_functions_snd_subset p.(functions) p r H_check_sc f H_in_f_pfs b H_b_in_bsf).
  Qed.
    

  Lemma check_program_complete_subset:
    forall p r,
      (forall f,
          In f p.(functions) -> forall b, In b f.(blocks) -> snd_block_info_sub p r f.(name) b) ->
      check_program_subset p r = true.
  Proof.
    intros p r H_snd.
    unfold check_program_subset.
    apply (check_functions_complete_subset p.(functions) p r H_snd).
  Qed.

  Lemma check_program_correct_subset:
    forall p r,
      (forall f,
          In f p.(functions) ->
          forall b, In b f.(blocks) ->
                    snd_block_info_sub p r f.(name) b) <-> check_program_subset p r = true.
    Proof.
      intros p r.
      split.
      - apply check_program_complete_subset.
      - apply check_program_snd_subset.
    Qed.

  (* This is the main theorem about the livness checking procedure,
  without refering to live_in and live_ot. Using snd_info, we can
  replace snd_all_blocks_info_sub by one that is based on live_in and
  live_out --- should be done later *)
  Lemma check_valid_prog_correct_subset:
    forall p r,
      CFGProgD.valid_program p ->
      snd_all_blocks_info_sub p r <-> check_program_subset p r = true.
  Proof.
    intros p r H_valid_p.
    rewrite <- check_program_correct_subset.
    unfold snd_all_blocks_info_sub.
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



End Liveness_checker_snd.
