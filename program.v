(*

Data structures for CFG-YUL programs

*)

Require Export Coq.Lists.List.
Import ListNotations.
Require Export Coq.Strings.String.
Require Export FORYU.evm_dialect.


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


Module FunctionName.
  (* YUL Function names represented as strings. *)
  Definition t := string.

  Definition eqb (f1 f2 : t) : bool :=
    String.eqb f1 f2.
End FunctionName.


Module ExitInfo.
  Inductive t : Set := 
  | ConditionalJump (cond_var : YULVariable.t) 
                    (target_if_true : BlockID.t) 
                    (target_if_false : BlockID.t)
  | Jump (target : BlockID.t)
  | ReturnBlock (return_values : list YULVariable.t) (* I believe they are always vars *)
  | Terminated.
End ExitInfo.


Module YULVariableMap.
  (* Map between YUL variables to apply renamings in phi functions *)
  Definition t := YULVariable.t -> YULVariable.t.
  
  (* The empty map is the identity function. *)
  Definition empty : t := fun x => x.
End YULVariableMap.


Module PhiInfo.
  (* A phi function is a mapping from an entry BlockID to the mapping of YULVariables to
     apply *)
  Definition t := BlockID.t -> YULVariableMap.t.

  (* The empty phi function maps every block ID to the empty map. *)
  Definition empty : t := fun _ => YULVariableMap.empty.
End PhiInfo.


Module Instruction (D: DIALECT).
(* An instruction is a pair of a block ID and a YUL variable. *)
   Record t : Type := {
    input : list (YULVariable.t + D.value_t); (* Either a variable or a value *)
    output : list YULVariable.t; (* Output variables *)
    op : FunctionName.t + D.opcode_t;
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
  (* Block of code of CFG-YUL *)
  Record t : Type := {
    bid : BlockID.t;
    phi_function : PhiInfo.t;
    exit_info : ExitInfo.t;
    instructions : list (InstructionD.t); (* List of instructions in the block *)
  }.
  
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
  
End SmartContract.