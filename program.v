(*

Data structures for CFG-YUL programs

*)

Require Export Coq.Lists.List.
Import ListNotations.
Require Export Coq.Strings.String.
Require Export FORYU.evm_dialect.
Require Import Orders.
Require Import OrdersEx.
Require Import MSets.
Require Import Arith.


Global Open Scope string_scope.
Global Open Scope Z_scope.


Module BlockID.
  (* A block ID is a natural number. *)
  Definition t := nat.

  Definition eqb (b1 b2 : t) : bool :=
    Nat.eqb b1 b2.

End BlockID.

Module YULVariable.
  (* YUL variables are represented as natural numbers. *)
  Definition t := nat.

  Definition eqb (v1 v2 : t) : bool :=
    Nat.eqb v1 v2.

End YULVariable.

Module VarSet := Make Nat_as_OT.


Module SimpleExpr (D: DIALECT).
  Definition t : Type := YULVariable.t + D.value_t.

End SimpleExpr.

Module FunctionName.
  (* YUL Function names represented as strings. *)
  Definition t := string.

  Definition eqb (f1 f2 : t) : bool :=
    String.eqb f1 f2.

End FunctionName.


Module ExitInfo (D: DIALECT).
  Module SimpleExprD := SimpleExpr(D).
  
  Inductive t : Type := 
  | ConditionalJump (cond_var : YULVariable.t) 
                    (target_if_true : BlockID.t) 
                    (target_if_false : BlockID.t)
  | Jump (target : BlockID.t)
  | ReturnBlock (return_values : list SimpleExprD.t) (* I believe they are always vars *)
  | Terminated.
       
End ExitInfo.


Module YULVariableMap (D: DIALECT).
  Module SimpleExprD := SimpleExpr(D).

  (* Map between YUL variables to apply renamings in phi functions *)
  (* Definition t := YULVariable.t -> YULVariable.t. *)
  Definition t := list (YULVariable.t * SimpleExprD.t).
  (* A pair (dest, origin) means that variable 'x' must take the value of the variable 'origin' *)
 
  Definition empty : t := [].

End YULVariableMap.


Module PhiInfo (D: DIALECT).
  Module YULVariableMapD := YULVariableMap(D).
  (* A phi function is a mapping from an entry BlockID to the mapping of YULVariables to
     apply *)
  Definition t := BlockID.t -> YULVariableMapD.t.

  (* The empty phi function maps every block ID to the empty map. *)
  Definition empty : t := fun _ => YULVariableMapD.empty.
End PhiInfo.


Module Instruction (D: DIALECT).

  Inductive aux_inst_t : Type :=
    | ASSIGN. (* This is to allow a simple assignment of the form [v1...vk] := [exp1...expk] at the level of YUL *)
  
  (* An instruction is a pair of a block ID and a YUL variable. *)
   Record t : Type := {
    input : list (YULVariable.t + D.value_t); (* Either a variable or a value *)
    output : list YULVariable.t; (* Output variables *)
    op : FunctionName.t + D.opcode_t + aux_inst_t;
  }.

  Lemma eq_split: forall i1 i2 : Instruction.t, 
    i1.(input) = i2.(input) ->
    i1.(output) = i2.(output) ->
    i1.(op) = i2.(op) ->
    i1 = i2.
  Proof.
    intros i1 i2 eq_input eq_output eq_op.
    destruct i1 as [input1 output1 op1].
    destruct i2 as [input2 output2 op2].
    simpl in eq_input.
    simpl in eq_output.
    simpl in eq_op.
    rewrite -> eq_input.
    rewrite -> eq_output.
    rewrite -> eq_op.
    reflexivity.
  Qed.
End Instruction.

(*
How to access the entries of an Instruction i of type Instruction(D).t? 
- i.(Instruction.input) to access the input
- i.(Instruction.output) to access the output
- i.(Instruction.op) to access the operation
*)

Module Block (D: DIALECT).
  Module InstructionD := Instruction(D). (* Required to access Instruction(D) *)
  Module PhiInfoD := PhiInfo(D).
  Module ExitInfoD := ExitInfo(D).
  
  (* Block of code of CFG-YUL *)
  Record t : Type := {
    bid : BlockID.t;
    phi_function : PhiInfoD.t;
    exit_info : ExitInfoD.t;
    instructions : list (InstructionD.t); (* List of instructions in the block *)
    }.

  Definition is_return_block (b : t) :=
    match b.(exit_info) with
    | ExitInfoD.ReturnBlock rs => Some rs
    | _ => None
    end.

  Definition is_jump_block (b : t) :=
    match b.(exit_info) with
    | ExitInfoD.Jump bid => Some bid
    | _ => None
    end.

  Definition is_cond_jump_block (b : t) :=
    match b.(exit_info) with
    | ExitInfoD.ConditionalJump v bid1 bid2 => Some (v,bid1,bid2)
    | _ => None
    end.

  Definition is_terminated_block (b : t) :=
    match b.(exit_info) with
    | ExitInfoD.Terminated => true
    | _ => false
    end.

End Block.


Module Function (D: DIALECT).
  Module BlockD := Block(D). (* Required to access Block(D) *)
  
    (* A function is a collection of blocks, an entry block ID, and a name. *)
  Record t : Type := {
    name : FunctionName.t;
    arguments : list YULVariable.t; (* Input parameters *)
    num_outputs : nat; (* Number of output parameters *)
    blocks : list BlockD.t; (* List of blocks *)
    entry_block_id : BlockID.t; (* The ID of the entry block. *)
  }.

  Definition get_block (f: t) (bid: BlockID.t) : option BlockD.t :=
    match List.find (fun b => BlockID.eqb b.(BlockD.bid) bid) f.(blocks) with
    | Some block => Some block
    | None => None
    end.
  
   Definition valid_function (f: t) :=
    forall b,
      In b (blocks f) <-> get_block f b.(BlockD.bid) = Some b.
   
End Function.


Module SmartContract (D: DIALECT).
  Module FunctionD := Function(D). (* Required to access Function(D) *)
  Module BlockD := FunctionD.BlockD.
  
  (* A smart contract is a collection of functions and a main function. *)
  Record t : Type := {
    name : string; (* Name of the smart contract *)
    functions : list FunctionD.t; (* List of functions in the smart contract *)
    main: FunctionName.t; (* The main function of the smart contract *)
  }.
 
  Definition get_function (sc: t) (fname: FunctionName.t) : option FunctionD.t :=
    match List.find (fun f => FunctionName.eqb f.(FunctionD.name) fname) sc.(functions) with
    | Some func => Some func
    | None => None
    end.

  Definition get_block (sc: t) (fname: FunctionName.t) (bid: BlockID.t) : option BlockD.t :=
    match get_function sc fname with
    | Some func => FunctionD.get_block func bid
    | None => None
    end.

  Definition get_instruction (sc: t) (fname: FunctionName.t) (bid: BlockID.t) (index: nat) : option BlockD.InstructionD.t :=
    match get_block sc fname bid with
    | Some block =>
        List.nth_error block.(BlockD.instructions) index 
    | None => None
    end.

  Definition get_first_block_id (sc: t) (fname: FunctionName.t) : option BlockID.t :=
    match get_function sc fname with
    | Some func => Some func.(FunctionD.entry_block_id)
    | None => None
    end.

  Definition all_function_name_are_different  (p: t) :=
      forall f,
        In f (functions p) <-> get_function p f.(FunctionD.name) = Some f.

  Definition all_function_are_valid  (p: t) :=
    forall f,
      In f (functions p) -> FunctionD.valid_function f.

  Definition valid_smart_contract (p: t) :=
    all_function_name_are_different p /\ all_function_are_valid p.

  Lemma valid_p_vs_get_block:
    forall p,
      valid_smart_contract p ->
      forall fname bid b,
        get_block p fname bid = Some b <->
          exists f, In f p.(functions)  /\ In b f.(FunctionD.blocks) /\ FunctionName.eqb f.(FunctionD.name) fname = true /\ BlockID.eqb b.(BlockD.bid) bid = true.
  Proof.
    intros p H_valid_p.
    intros f bid b.
    split.
    - intros H_get_block.
      unfold get_block in H_get_block.
      destruct (get_function p f) as [func|] eqn:E_get_function; try discriminate.
      unfold get_function in E_get_function.
      destruct (find (fun f0 : FunctionD.t => FunctionName.eqb (FunctionD.name f0) f)) as [func'|] eqn:E_find_func'; try discriminate.
      injection E_get_function as H_func'_eq_func.
      subst func'.

      unfold FunctionD.get_block in H_get_block.
      destruct (find (fun b : FunctionD.BlockD.t => BlockID.eqb (FunctionD.BlockD.bid b) bid) (FunctionD.blocks func)) as [b'|] eqn:E_find_b'; try discriminate.
        
      injection H_get_block as H_b'_eq_b.
      subst b'.

      pose proof (find_some (fun f0 : FunctionD.t => FunctionName.eqb (FunctionD.name f0) f) (functions p) E_find_func' ) as [H_in_func_pfs H_func_name_eqb_f].
      
      pose proof (find_some (fun b : FunctionD.BlockD.t => BlockID.eqb (FunctionD.BlockD.bid b) bid) (FunctionD.blocks func) E_find_b') as [H_in_b_funcbs H_b_bid_eqb_bid].

      exists func.
      repeat split.
      + apply H_in_func_pfs.
      + apply H_in_b_funcbs.
      + apply H_func_name_eqb_f.
      + apply H_b_bid_eqb_bid.

    - intros H_exists_f0.
      destruct H_exists_f0 as [f0 [In_f0_pfs [In_b_f0bs [H_f0_name_eqb_f H_b_bid_eqb_b]]]].

      unfold FunctionName.eqb in H_f0_name_eqb_f.
      apply String.eqb_eq in H_f0_name_eqb_f.
      subst f.

      unfold BlockID.eqb in H_b_bid_eqb_b.
      apply Nat.eqb_eq in H_b_bid_eqb_b.
      subst bid.
      
      
      unfold valid_smart_contract in H_valid_p.
      destruct H_valid_p as [H_all_fname_diff H_all_f_valid].

      
      unfold all_function_name_are_different in H_all_fname_diff.
      unfold all_function_are_valid in H_all_f_valid.

      unfold get_block.

      pose proof (H_all_fname_diff f0) as H_get_function_f0.
      pose proof (H_all_f_valid f0 In_f0_pfs) as H_f0_valid.
      unfold FunctionD.valid_function in H_f0_valid.

      rewrite H_get_function_f0 in In_f0_pfs.
      rewrite In_f0_pfs.
      
      rewrite H_f0_valid in In_b_f0bs.
      apply In_b_f0bs.
  Qed.

End SmartContract.
