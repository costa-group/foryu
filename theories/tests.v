Require Export FORYU.program.
Require Export FORYU.semantics.
Import ListNotations.

(* Needed for print-debugging with Reduction Effects 
   (https://github.com/coq-community/reduction-effects)
   even if the print/print_id are in other files
*)
From ReductionEffect Require Import PrintingEffect.

(******** Tests ********)

(* Note how EVM definitions are defined from the top-most 
   specialized module down to the bottom-most, because 
   if we define EVMInstruction as

      Module EVMInstruction := Instruction(EVMDialect).

   then there are compilation errors because
   
      EVMInstruction.t =/= EVMBlock.InstructionD.t
   *)
Module EVMSmallStep := SmallStep(EVMDialect).
Module EVMSmartContract := EVMSmallStep.SmartContractD.
Module EVMFunction := EVMSmartContract.FunctionD.
Module EVMBlock := EVMFunction.BlockD.
Module EVMInstruction := EVMBlock.InstructionD.
Module EVMState := EVMSmallStep.StateD.


Definition i1 : EVMInstruction.t := (* v2 := ADD v0 555 *)
  {| EVMInstruction.input := [inl 0%nat; inr 555];
     EVMInstruction.output := [2%nat];
     EVMInstruction.op := inl (inr EVM_opcode.ADD) |}.

Definition i2 : EVMInstruction.t := (* v1 := ISZERO v3 *)
  {| EVMInstruction.input := [inl 3%nat];
     EVMInstruction.output := [1%nat];
     EVMInstruction.op := inl (inr EVM_opcode.ISZERO) |}.

Definition i3 : EVMInstruction.t := (* v0, v2 := myfunct 333 *)
  {| EVMInstruction.input := [inr 333];
     EVMInstruction.output := [0%nat; 2%nat];
     EVMInstruction.op := inl (inl "myfunct") |}.

Fixpoint has_input_vars_list (l: list (YULVariable.t + EVMDialect.value_t)) :=
  match l with
  | [] => false
  | inl v :: _ => true
  | inr _ :: r => has_input_vars_list r
  end.     

Definition has_input_vars (ins: EVMInstruction.t) : bool :=
  has_input_vars_list ins.(EVMInstruction.input).

(* 
Compute (has_input_vars i1). (* Should return true *)  
Compute (has_input_vars i3). (* Should return false *)
*)

Definition b1 : EVMBlock.t :=
  {| EVMBlock.bid := 1%nat;
     EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
     EVMBlock.exit_info := EVMBlock.ExitInfoD.Jump 2%nat;
     EVMBlock.instructions := [i1; i2] |}.

Definition b2 : EVMBlock.t :=
  {| EVMBlock.bid := 2%nat;
     EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
     EVMBlock.exit_info := EVMBlock.ExitInfoD.ReturnBlock [inl 0%nat; inl 1%nat];
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

(* Print sc1. *)



Section RunningExample.

(* Original Yul program 

{
    function f() -> v1 {
        v0 := 0x0202
        v1 := mul(v0, 0x2)
    }
    
   let v0 := f()
	sstore(0x01, v0)
}

*)

(* Main function *)
Definition instr_call_f : EVMInstruction.t :=
   (* let v0 := f() *)
   {| EVMInstruction.input := [];
      EVMInstruction.output := [0%nat];
      EVMInstruction.op := inl (inl "f") |}.

Definition instr_sstore : EVMInstruction.t :=
   (* sstore(0x01, v0) *)
   {| EVMInstruction.input := [inl 0%nat; inr 1];
      EVMInstruction.output := [];
      EVMInstruction.op := inl (inr EVM_opcode.SSTORE) |}.

Definition main_block_0 : EVMBlock.t :=
   {| EVMBlock.bid := 0%nat;
      EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
      EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
      EVMBlock.instructions := [ instr_call_f ; instr_sstore ]
   |}.

Definition func_main : EVMFunction.t :=
   {| EVMFunction.name := "main";
      EVMFunction.arguments := [];
      EVMFunction.num_outputs := 0;
      EVMFunction.blocks := [ main_block_0 ];
      EVMFunction.entry_block_id := 0%nat
   |}.


(* "f" function *)
Definition instr_mul : EVMInstruction.t :=
   (* v1 := mul(v0, 0x2) simplified wrt. v0 -> 0x0202 *)
   {| EVMInstruction.input := [inr 0x2; inr 0x0202];
      EVMInstruction.output := [ 1%nat ];
      EVMInstruction.op := inl (inr EVM_opcode.MUL) |}.

Definition f_block_0 : EVMBlock.t :=
   {| EVMBlock.bid := 0%nat;
      EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
      EVMBlock.exit_info := EVMBlock.ExitInfoD.ReturnBlock [inl 1%nat];
      EVMBlock.instructions := [ instr_mul ]
   |}.

Definition func_f : EVMFunction.t :=
   {| EVMFunction.name := "f";
      EVMFunction.arguments := [];
      EVMFunction.num_outputs := 1;
      EVMFunction.blocks := [ f_block_0 ];
      EVMFunction.entry_block_id := 0%nat
   |}.   

Definition smart_contract : EVMSmartContract.t :=
   {| EVMSmartContract.name := "test";
      EVMSmartContract.functions := [ func_f ; func_main ];
      EVMSmartContract.main := "main" |}. 

(* Print smart_contract. *)

Definition initial_state : EVMState.t :=
  EVMState.empty.


Eval cbv in (
   let s0 := EVMState.initial_main in
   let s1 := EVMSmallStep.step s0 smart_contract in
   print (s0, s1)
   (* 
   let s2 := EVMSmallStep.step s1 smart_contract in
   let s3 := EVMSmallStep.step s2 smart_contract in
   let s4 := EVMSmallStep.step s3 smart_contract in
   let s5 := EVMSmallStep.step s4 smart_contract in
   (s2, s3, s4, s5)
   *)
   ).


Eval cbv in (
   let s  := EVMState.initial_main in
   let s' := EVMSmallStep.eval 10 s smart_contract in
   print s'
).



End RunningExample.


(******** End of tests ********)      












