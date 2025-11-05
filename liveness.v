Require Import FORYU.state.
Require Import FORYU.program.
Require Import FORYU.semantics.
Require Import Orders.
Require Import OrdersEx.
Require Import MSets.
Require Import MSetList.
Require Import Arith.


Module VarSet := Make Nat_as_OT.

Module Liveness (D: DIALECT).

  Module SmallStepD := SmallStep(D).
  Module StateD := SmallStepD.StateD.
  Module SmartContractD := SmallStepD.SmartContractD.
  Module FunctionD := SmartContractD.FunctionD.
  Module BlockD := SmartContractD.BlockD.
  Module InstructionD := BlockD.InstructionD.
  Module YULVariableMapD := BlockD.PhiInfoD.YULVariableMapD.
  Module SimpleExprD := BlockD.PhiInfoD.YULVariableMapD.SimpleExprD.
  
  Definition is_end_of_block (p : SmartContractD.t) (fname : FunctionName.t) (bid:  BlockID.t) (pc: nat) :=
    match (SmartContractD.get_instruction p fname bid pc) with
    | None => false
    | Some _ => true
    end.

  (* define a relaion between a list an its corresponding set *)
  Inductive list_eq_set : list nat -> VarSet.t -> Prop :=
  | empty:
    list_eq_set nil VarSet.empty
  | rec (x: nat) (xs: list nat) (s1 s2: VarSet.t):
    list_eq_set xs s1 ->
    VarSet.add x s1 = s2 ->
    list_eq_set (x::xs) s2.

  (* convert a list to a set *)
  Fixpoint list_to_set (l : list nat) : VarSet.t :=
    match l with
    | nil => VarSet.empty
    | x::xs => VarSet.add x (list_to_set xs)
    end.

  Lemma list_to_set_snd:
    forall l s, list_to_set l = s -> list_eq_set l s.
  Proof.
    induction l as [| a l'].
    - intros s.
      intros H.
      simpl in H.
      rewrite <- H.
      apply empty.
    - intros s.
      intros H.
      simpl in H.
      apply rec with (s1 := (list_to_set l')).
      + apply (IHl' (list_to_set l')).
        reflexivity.
      + apply H.
  Qed.

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


  (** This is the defintion of liveness
      =================================

      It is the way the standard live property is defined in dataflow
      analysis.

      'live_varset p f id pc x' means that the set of variables 'x' is
      live at program point 'p/f/id/pc'. I.e., these variables are
      used in the rest of the execution at least once. 

   **)
  
  Inductive live_varset  (p : SmartContractD.t) : FunctionName.t -> BlockID.t -> nat -> VarSet.t -> Prop :=

  (* At an exit block, only the return variables are alive *)
  | end_of_block_exit_pp (fname : FunctionName.t) (bid :  BlockID.t) (pc : nat) (b: BlockD.t) (rs: list SimpleExprD.t) (s: VarSet.t):
    SmartContractD.get_block p fname bid = Some b -> (* the block exists *)
    is_end_of_block p fname bid pc = true -> (* p/fname/bid/pc corresponds to an end of a block *)
    BlockD.is_exit_block b = Some rs -> (* rs is the list of returned expressions *)
    list_to_set (extract_yul_vars rs) = s -> (* s is the set representing rs *)
    live_varset p fname bid pc s (* s is alive at  p/fname/bid/pc *)

  (* At the end of block with a with jump, the live variables are those a live at the entry of the next block + renaming wrt. the corresponding phi function *)
  | end_of_block_jump_pp (fname : FunctionName.t) (bid next_bid:  BlockID.t) (pc : nat) (b next_b: BlockD.t) (s s': VarSet.t):
    SmartContractD.get_block p fname bid = Some b -> (* the block exists *)
    is_end_of_block p fname bid pc = true -> (* p/fname/bid/pc corresponds to an end of a block *)
    BlockD.is_jump_block b = Some next_bid -> (* the block ends with a jump, and next_bid is the id of the next block *)
    live_varset p fname next_bid 0 s -> (* s is the set of live variables at p/fname/next_bid/0 *)
    SmartContractD.get_block p fname next_bid = Some next_b -> (* next_b is the block with id next_bid *)
    apply_phi (BlockD.phi_function next_b bid) s = s' -> (* apply -- in a reverse way -- the corresponding phi function on s to obain s' *)
    live_varset p fname bid pc s'  (* s' is alive at  p/fname/bid/pc *)

  (* At the end of block with a conditional jump, the live variables are those live at the entry of wither of the next next blocks -- after renaming wrt. the corresponding phi function -- and the conditional variable *)
  | end_of_block_cond_jump_pp (fname : FunctionName.t) (bid next_bid_if_true next_bid_if_false:  BlockID.t) (pc cond_var: nat) (b next_b_if_true next_b_if_false: BlockD.t) (s1 s1' s2 s2': VarSet.t):
    SmartContractD.get_block p fname bid = Some b -> (* the block exists *)
    is_end_of_block p fname bid pc = true ->  (* p/fname/bid/pc corresponds to an end of a block *)
    BlockD.is_cond_jump_block b = Some (cond_var, next_bid_if_true, next_bid_if_false) -> (* the block ends with a jump, and next_bid_if_true and next_bid_if_false are the identifiers of the next blocks *)
    live_varset p fname next_bid_if_true 0 s1 ->  (* s1 is the set of live variables at p/fname/next_bid_if_true/0 *)
    live_varset p fname next_bid_if_false 0 s2 -> (* s2 is the set of live variables at p/fname/next_bid_if_false/0 *)
    SmartContractD.get_block p fname next_bid_if_true = Some next_b_if_true -> (* next_b_if_true is the block with id next_bid_if_true *)
    SmartContractD.get_block p fname next_bid_if_false = Some next_b_if_false -> (* next_b_if_false is the block with id next_bid_if_false *)
    apply_phi (BlockD.phi_function next_b_if_true bid) s1 = s1' -> (* apply -- in a reverse way -- the corresponding phi function on s1 to obain s1' *)
    apply_phi (BlockD.phi_function next_b_if_false bid) s2 = s2' -> (* apply -- in a reverse way -- the corresponding phi function on s2 to obain s2' *)
    live_varset p fname bid pc (VarSet.add cond_var (VarSet.union s1' s2')) (* s1' \/ s2' is alive at  p/fname/bid/pc *)

  (* Execution of an instruction (opcode, function call, or a simple assignment) *)
  | instr_pp (fname : FunctionName.t) (bid :  BlockID.t) (pc : nat) (b: BlockD.t) (instr : InstructionD.t) (s outvars invars: VarSet.t):
    live_varset p fname bid (pc+1)%nat s -> (* s is the set of live vars at pc+1 *)
    SmartContractD.get_instruction p fname bid pc = Some instr -> (* 'instr' is the current instructions at p/fname/bid/pc *)
    list_eq_set (extract_yul_vars instr.(SmartContractD.BlockD.InstructionD.input)) invars -> (* invars is the set of input variables *)
    list_eq_set instr.(SmartContractD.BlockD.InstructionD.output) outvars -> (* outvars is the set of output variables *)
    live_varset p fname bid pc (VarSet.union (VarSet.diff s outvars) invars). (* (s\outvars) \/ invars is alive at  p/fname/bid/pc *)

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
