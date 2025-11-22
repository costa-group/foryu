(* 
FORYU: Automatic translation for liveness analysis
Smart contract: constant_variables.sol 
Date: 2025-11-22 14:47:37.562522
*)

Require Export FORYU.program.
Require Export FORYU.semantics.
Require Export FORYU.liveness.
Import ListNotations.

Module EVMLiveness := Liveness(EVMDialect).
Module EVMSmallStep := EVMLiveness.SmallStepD.
Module EVMSmartContract := EVMSmallStep.SmartContractD.
Module EVMFunction := EVMSmartContract.FunctionD.
Module EVMBlock := EVMFunction.BlockD.
Module EVMInstruction := EVMBlock.InstructionD.
Module EVMState := EVMSmallStep.StateD.

Section Translation.

Definition sc_tr : EVMSmartContract.t :=
       {| EVMSmartContract.name := "constant_variables.sol";
           EVMSmartContract.functions := [
      {| EVMFunction.name := "constant_variables_sol__Foo__Foo_17__Foo_17_deployed__entry";
             EVMFunction.arguments := [];
             EVMFunction.num_outputs := 0;
             EVMFunction.blocks := [
    
                {| EVMBlock.bid := 0%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x00; inr 0x00 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.REVERT)
                  |}]
                |}
             ];
             EVMFunction.entry_block_id := 0%nat
          |};
      {| EVMFunction.name := "constant_variables_sol__Foo__Foo_17__entry";
             EVMFunction.arguments := [];
             EVMFunction.num_outputs := 0;
             EVMFunction.blocks := [
    
                {| EVMBlock.bid := 0%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 2%nat 2%nat 1%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 0%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.MEMORYGUARD)
                  |};
                  {| EVMInstruction.input := [ inl 0%nat; inr 0x40 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |};
                  {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 2%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.CALLVALUE)
                  |}]
                |};
                {| EVMBlock.bid := 2%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 4%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.DATASIZE)
                  |};
                  {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 5%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.DATAOFFSET)
                  |};
                  {| EVMInstruction.input := [ inl 4%nat; inl 5%nat; inl 0%nat ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.CODECOPY)
                  |};
                  {| EVMInstruction.input := [ inl 4%nat; inl 0%nat ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.RETURN)
                  |}]
                |};
                {| EVMBlock.bid := 1%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x00; inr 0x00 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.REVERT)
                  |}]
                |}
             ];
             EVMFunction.entry_block_id := 0%nat
          |}];
           EVMSmartContract.main := "constant_variables_sol__Foo__Foo_17__Foo_17_deployed__entry" 
       |}.

Definition liveness_info : FunctionName.t -> option EVMLiveness.fun_live_info_t :=
fun fname =>
   match fname with 
   | "constant_variables_sol__Foo__Foo_17__Foo_17_deployed__entry" => Some (
      fun blockid =>
         match blockid with 
         | 0%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])
         | _ => None
         end )
   | "constant_variables_sol__Foo__Foo_17__entry" => Some (
      fun blockid =>
         match blockid with 
         | 0%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [ 0%nat ])         
         | 2%nat => Some (EVMLiveness.list_to_set [ 0%nat ], EVMLiveness.list_to_set [  ])         
         | 1%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])
         | _ => None
         end )
   | _ => None
   end.

(* Launches liveness check *)
Compute (EVMLiveness.check_smart_contract sc_tr liveness_info).

End Translation.
        