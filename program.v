(*

Data structures for CFG-YUL programs

*)

Require Export Coq.Lists.List.
Require Export Coq.Strings.String.
Require Export FORYU.evm_dialect.


Global Open Scope string_scope.
Global Open Scope Z_scope.


Module BlockID.
  (* A block ID is a natural number. *)
  Definition t := nat.
End BlockID.


Module YULVariable.
  (* YUL variables are represented as natural numbers. *)
  Definition t := nat.
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
                    (target_if_zero : BlockID.t) 
                    (target_if_nonzero : BlockID.t)
  | Jump (target : BlockID.t)
  | ReturnBlock (return_values : list YULVariable.t) (* I believe they are always vars *)
  | Terminated.
End ExitInfo.


Module YULVariableMap.
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


Module Instruction (D: Dialect).
(* An instruction is a pair of a block ID and a YUL variable. *)
  Record t : Type := {
    input : list (YULVariable.t + D.value_t); (* Either a variable or a value *)
    output : list YULVariable.t; (* Output variables *)
    op : FunctionName.t + D.opcode_t;
  }.

  Lemma eq_split: forall i1 i2 : Instruction.t, 
    i1.(Instruction.input) = i2.(Instruction.input) ->
    i1.(Instruction.output) = i2.(Instruction.output) ->
    i1.(Instruction.op) = i2.(Instruction.op) ->
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
(* ____TO_SAMIR____ How can we parameterize Instructions with the dialect ?*)

Module EVMInstruction := Instruction(EVMDialect). 

Definition test : EVMInstruction.t :=
  {| EVMInstruction.input := nil;
     EVMInstruction.output := nil;
     EVMInstruction.op := inr EVM_opcode.ADD |}.

Check test.

(*
How to access the entries of an Instruction i of type Instruction.t? 
- i.(Instruction.input) to access the input
- i.(Instruction.output) to access the output
- i.(Instruction.op) to access the operation
*)

 
Module Block (D: Dialect).
  (* Block of code of CFG-YUL *)
  Record t : Set := {
    bid : BlockID.t;
    phi_function : PhiInfo.t;
    exit_info : ExitInfo.t;
    instructions : list Instruction(D);
  }.
End Block.


Module Function.
  (* A function is a collection of blocks, an entry block ID, and a name. *)
  Record t : Set := {
    name : FunctionName.t;
    arguments : list YULVariable.t; (* Input parameters *)
    num_outputs : nat; (* Number of output parameters *)
    blocks : list Block.t; (* List of blocks *)
    entry_block_id : BlockID.t; (* The ID of the entry block. *)
  }.
End Function.


Module SmartContract.
  (* A smart contract is a collection of functions and a name. *)
  Record t : Set := {
    name : string; (* Name of the smart contract *)
    functions : list Function.t; (* List of functions in the smart contract *)
    main: Function.t; (* The main function of the smart contract *)
  }.
End SmartContract.
