Require Import FORYU.state.
Require Import FORYU.program.
Require Import FORYU.semantics.
Require Import Orders.
Require Import OrdersEx.
Require Import MSets.
Require Import Arith.
Require Import List.
Import ListNotations.
Require Import Coq.Relations.Relation_Operators.
Require Import stdpp.prelude.
Require Import stdpp.relations. (* This is where nsteps lives *)


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
  Module CallStackD := StateD.CallStackD.
  Module StackFrameD := CallStackD.StackFrameD.
  Module VariableAssignmentD := StackFrameD.VariableAssignmentD.
  
  (* convert a list to a set *)
  Fixpoint list_to_set (l : list nat) : VarSet.t :=
    match l with
    | nil => VarSet.empty
    | x::xs => VarSet.add x (list_to_set xs)
    end.
    
  (* extracts a list of variables from a list of simple expressions (a
    simple expression is either a variable or of type D.t *)
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

  (* applies the inverse of the phi function 'l' (pairs of variable
  and simple expressions) to the set of expressions 's'.  *)
  Fixpoint apply_inv_phi (l : YULVariableMapD.t) (s: VarSet.t) :=
    match l with
    | nil => s
    | (dest,orig)::vs =>
        match orig with
        | inl var =>
            if (VarSet.mem dest s) then
              apply_inv_phi vs (VarSet.add var (VarSet.remove dest s))
            else
              apply_inv_phi vs s
        | inr _ =>
            apply_inv_phi vs (VarSet.remove dest s)
        end
    end.

    
  Definition prop_live_set_bkw_instr (i: InstructionD.t) (s: VarSet.t) : VarSet.t :=
    let inset := list_to_set (extract_yul_vars i.(InstructionD.input)) in
    let outset := list_to_set i.(InstructionD.output) in
    (VarSet.union (VarSet.diff s outset) inset).

    
  Fixpoint prop_live_set_bkw_aux (n: nat) (l_rev: list InstructionD.t) (s: VarSet.t) : VarSet.t :=
    match n with
    | 0%nat => s
    | S n' =>
        match l_rev with
        | nil => s
        | i::l_rev' =>
            prop_live_set_bkw_aux n' l_rev' (prop_live_set_bkw_instr i s)
        end
    end.


  Definition prop_live_set_bkw (l: list InstructionD.t) (s: VarSet.t) : VarSet.t :=    
    prop_live_set_bkw_aux  (length l) (rev l) s.

  Definition add_jump_var_if_applicable (b: BlockD.t) (s: VarSet.t) :=
    match b.(BlockD.exit_info) with
    | ExitInfoD.ConditionalJump cond_var _ _ => VarSet.add cond_var s
    | _ => s
      end.

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
                        VarSet.equal b_out_info (apply_inv_phi (BlockD.phi_function next_b b.(BlockD.bid)) next_b_in_info)
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
                                                           (apply_inv_phi (BlockD.phi_function next_b_if_true b.(BlockD.bid)) next_b_ift_in_info)
                                                           (apply_inv_phi (BlockD.phi_function next_b_if_false b.(BlockD.bid)) next_b_iff_in_info))
                            end
                        end
                    end
                end
            end
        end
    end.


  Definition check_live (p: SmartContractD.t) (r: sc_live_info_t) (f: FunctionName.t) (b: BlockD.t) : bool :=
    if (check_live_in r f b) then check_live_out p r f b else false.


  Fixpoint check_blocks (bs: list BlockD.t) (fname: FunctionName.t) (p: SmartContractD.t) (r: sc_live_info_t) :=
    match bs with
    | nil => true
    | b::bs' => if (check_live p r fname b)
                then check_blocks bs' fname p r
                else false
    end.


  Fixpoint check_functions (fs: list FunctionD.t) (p: SmartContractD.t) (r: sc_live_info_t) :=
    match fs with
    | nil => true
    | f::fs' => if (check_blocks f.(FunctionD.blocks) f.(FunctionD.name) p r)
                then check_functions fs' p r
                else false
    end.

  Definition check_smart_contract (p: SmartContractD.t) (r: sc_live_info_t) :=
    check_functions p.(SmartContractD.functions) p r.


  (* A version that uses subset instead of equal *)

  Definition check_live_in_subset (r: sc_live_info_t) (f: FunctionName.t) (b: BlockD.t) : bool :=
    match (r f) with
    | None => false
    | Some f_info =>
        match f_info b.(BlockD.bid) with
        | None => false
        | Some (b_in_info,b_out_info) =>
            VarSet.subset (prop_live_set_bkw b.(BlockD.instructions) (add_jump_var_if_applicable b b_out_info)) b_in_info 
        end
    end.

  Definition check_live_out_subset (p: SmartContractD.t) (r: sc_live_info_t) (f: FunctionName.t) (b: BlockD.t) : bool :=
    match (r f) with
    | None => false
    | Some f_info =>
        match (f_info b.(BlockD.bid)) with
        | None => false
        | Some (b_in_info,b_out_info) =>
            match b.(BlockD.exit_info) with
            | ExitInfoD.Terminated =>
                VarSet.subset VarSet.empty b_out_info
            | ExitInfoD.ReturnBlock rs => 
                VarSet.subset (list_to_set (extract_yul_vars rs)) b_out_info
            | ExitInfoD.Jump next_bid =>
                match (SmartContractD.get_block p f next_bid) with
                | None => false
                | Some next_b =>
                    match (f_info next_bid) with
                    | None => false
                    | Some (next_b_in_info,next_b_out_info) =>
                        VarSet.subset (apply_inv_phi (BlockD.phi_function next_b b.(BlockD.bid)) next_b_in_info) b_out_info
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
                                VarSet.subset (VarSet.union
                                                 (apply_inv_phi (BlockD.phi_function next_b_if_true b.(BlockD.bid)) next_b_ift_in_info)
                                                 (apply_inv_phi (BlockD.phi_function next_b_if_false b.(BlockD.bid)) next_b_iff_in_info)) b_out_info 
                            end
                        end
                    end
                end
            end
        end
    end.

  
  Definition check_live_subset (p: SmartContractD.t) (r: sc_live_info_t) (f: FunctionName.t) (b: BlockD.t) : bool :=
    if (check_live_in_subset r f b) then check_live_out_subset p r f b else false.

  Fixpoint check_blocks_subset (bs: list BlockD.t) (fname: FunctionName.t) (p: SmartContractD.t) (r: sc_live_info_t) :=
    match bs with
    | nil => true
    | b::bs' => if (check_live_subset p r fname b)
                then check_blocks_subset bs' fname p r
                else false
    end.


  Fixpoint check_functions_subset (fs: list FunctionD.t) (p: SmartContractD.t) (r: sc_live_info_t) :=
    match fs with
    | nil => true
    | f::fs' => if (check_blocks_subset f.(FunctionD.blocks) f.(FunctionD.name) p r)
                then check_functions_subset fs' p r
                else false
    end.
  
  Definition check_smart_contract_subset (p: SmartContractD.t) (r: sc_live_info_t) :=
    check_functions_subset p.(SmartContractD.functions) p r.

  (* end of version with subset *)
  
  Fixpoint nodupb {A : Type} (eqb : A -> A -> bool) (l : list A) : bool :=
    match l with
    | nil => true
    | h :: t => (negb (existsb (eqb h) t)) && (nodupb eqb t)
    end.

  Lemma nodup_NoDup {A: Type}:
    forall (eqb: A -> A -> bool),
      (forall a b, eqb a b = true -> a = b) ->
      forall l,
        nodupb eqb l = true -> NoDup l.
  Proof.
    intros eqb H_eqb_eq.
    induction l as [|a l'].
    - intros.
      apply NoDup_nil_2.
    - intros H_nodupb.
      apply NoDup_cons_2.
      + simpl in H_nodupb.
        apply andb_prop in H_nodupb.
        destruct H_nodupb as [H_nodupb_l H_nodupb_r].
        rewrite negb_true_iff in H_nodupb_l.
        pose proof (@existb_True A).
        Admitted.
  
  Definition all_block_ids_are_different (f: FunctionD.t): bool :=
    nodupb (fun b1 b2 => Nat.eqb b1.(BlockD.bid) b2.(BlockD.bid)) f.(FunctionD.blocks).

  Definition check_valid_function (f: FunctionD.t): bool :=
    all_block_ids_are_different f.
  
  Definition check_valid_functions (l: list FunctionD.t): bool :=
    fold_right (fun b a => a && check_valid_function b) true l.

  Definition check_function_names_are_different (l: list FunctionD.t): bool :=
    nodupb (fun f1 f2 => String.eqb f1.(FunctionD.name) f2.(FunctionD.name)) l.

  Definition smart_contrac (p: SmartContractD.t): bool :=
    check_function_names_are_different p.(SmartContractD.functions) &&
    check_valid_functions p.(SmartContractD.functions).
    
End Liveness.
