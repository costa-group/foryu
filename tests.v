Require Export FORYU.program.
Import ListNotations.

(******** Tests ********)

(* Note how EVM definitions are defined from the top-most 
   specialized module down to the bottom-most, because 
   if we define EVMInstruction as

      Module EVMInstruction := Instruction(EVMDialect).

   then there are compilation errors because
   
      EVMInstruction.t =/= EVMBlock.InstructionD.t
   *)
Module EVMSmartContract := SmartContract(EVMDialect).
Module EVMFunction := EVMSmartContract.FunctionD.
Module EVMBlock := EVMFunction.BlockD.
Module EVMInstruction := EVMBlock.InstructionD.

Definition i1 : EVMInstruction.t := (* v2 := ADD v0 555 *)
  {| EVMInstruction.input := [inl 0%nat; inr 555];
     EVMInstruction.output := [2%nat];
     EVMInstruction.op := inr EVM_opcode.ADD |}.

Definition i2 : EVMInstruction.t := (* v1 := ISZERO v3 *)
  {| EVMInstruction.input := [inl 3%nat];
     EVMInstruction.output := [1%nat];
     EVMInstruction.op := inr EVM_opcode.ISZERO |}.

Definition i3 : EVMInstruction.t := (* v0, v2 := myfunct 333 *)
  {| EVMInstruction.input := [inr 333];
     EVMInstruction.output := [0%nat; 2%nat];
     EVMInstruction.op := inl "myfunct" |}.

Fixpoint has_input_vars_list (l: list (YULVariable.t + EVMDialect.value_t)) :=
  match l with
  | [] => false
  | inl v :: _ => true
  | inr _ :: r => has_input_vars_list r
  end.     

Definition has_input_vars (ins: EVMInstruction.t) : bool :=
  has_input_vars_list ins.(EVMInstruction.input).

Compute (has_input_vars i1). (* Should return true *)  
Compute (has_input_vars i3). (* Should return false *)

Definition b1 : EVMBlock.t :=
  {| EVMBlock.bid := 1%nat;
     EVMBlock.phi_function := PhiInfo.empty;
     EVMBlock.exit_info := ExitInfo.Jump 2%nat;
     EVMBlock.instructions := [i1; i2] |}.

Definition b2 : EVMBlock.t :=
  {| EVMBlock.bid := 2%nat;
     EVMBlock.phi_function := PhiInfo.empty;
     EVMBlock.exit_info := ExitInfo.ReturnBlock [0%nat; 1%nat];
     EVMBlock.instructions := [i3] |}.

Definition f1 : EVMFunction.t :=
  {| EVMFunction.name := "myfunc";
     EVMFunction.arguments := [0%nat; 1%nat];
     EVMFunction.num_outputs := 2;
     EVMFunction.blocks := [b1; b2];
     EVMFunction.entry_block_id := 1%nat |}.

Definition sc1 : EVMSmartContract.t :=
  {| EVMSmartContract.name := "MySmartContract";
     EVMSmartContract.functions := [f1];
     EVMSmartContract.main := "myfunc" |}.  

Print sc1.









