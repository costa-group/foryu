(* 
FORYU: Automatic translation for liveness analysis
Smart contract: function_modifier.sol 
Date: 2025-11-23 16:21:34.398290

Compile with:
$ coqc -R . FORYU filename.v

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
       {| EVMSmartContract.name := "function_modifier.sol";
           EVMSmartContract.functions := [
      {| EVMFunction.name := "function_modifier_sol__C__C_20__C_20_deployed__entry";
             EVMFunction.arguments := [];
             EVMFunction.num_outputs := 0;
             EVMFunction.blocks := [
    
                {| EVMBlock.bid := 0%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 5%nat 2%nat 1%nat;
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
                      EVMInstruction.output := [ 3%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.CALLDATASIZE)
                  |};
                  {| EVMInstruction.input := [ inr 0x04; inl 3%nat ];
                      EVMInstruction.output := [ 4%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.LT)
                  |};
                  {| EVMInstruction.input := [ inl 4%nat ];
                      EVMInstruction.output := [ 5%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ISZERO)
                  |}]
                |};
                {| EVMBlock.bid := 2%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x00; inr 0x00 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.REVERT)
                  |}]
                |};
                {| EVMBlock.bid := 1%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 11%nat 4%nat 3%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x00 ];
                      EVMInstruction.output := [ 7%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.CALLDATALOAD)
                  |};
                  {| EVMInstruction.input := [ inl 7%nat; inr 0xe0 ];
                      EVMInstruction.output := [ 9%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SHR)
                  |};
                  {| EVMInstruction.input := [ inl 9%nat; inr 0xab5ed150 ];
                      EVMInstruction.output := [ 11%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.EQ)
                  |}]
                |};
                {| EVMBlock.bid := 4%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Jump 2%nat;
                   EVMBlock.instructions := [ 
    ]
                |};
                {| EVMBlock.bid := 3%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 16%nat 6%nat 5%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x03 ];
                      EVMInstruction.output := [ 13%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.NOT)
                  |};
                  {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 14%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.CALLDATASIZE)
                  |};
                  {| EVMInstruction.input := [ inl 13%nat; inl 14%nat ];
                      EVMInstruction.output := [ 15%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADD)
                  |};
                  {| EVMInstruction.input := [ inr 0x00; inl 15%nat ];
                      EVMInstruction.output := [ 16%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SLT)
                  |}]
                |};
                {| EVMBlock.bid := 6%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 21%nat 9%nat 8%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x00 ];
                      EVMInstruction.output := [ 17%nat ];
                      EVMInstruction.op := inr EVMInstruction.ASSIGN
                  |};
                  {| EVMInstruction.input := [ inr 0x00 ];
                      EVMInstruction.output := [ 18%nat ];
                      EVMInstruction.op := inr EVMInstruction.ASSIGN
                  |};
                  {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 19%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.CALLVALUE)
                  |};
                  {| EVMInstruction.input := [ inl 19%nat ];
                      EVMInstruction.output := [ 20%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ISZERO)
                  |};
                  {| EVMInstruction.input := [ inl 20%nat ];
                      EVMInstruction.output := [ 21%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ISZERO)
                  |}]
                |};
                {| EVMBlock.bid := 5%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x00; inr 0x00 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.REVERT)
                  |}]
                |};
                {| EVMBlock.bid := 9%nat;
                   EVMBlock.phi_function := fun blockid => if BlockID.eqb blockid 6%nat then [(24%nat, inl 18%nat)] else if BlockID.eqb blockid 8%nat then [(24%nat, inl 23%nat)] else [];
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inl 24%nat; inl 0%nat ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |};
                  {| EVMInstruction.input := [ inr 0x20; inl 0%nat ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.RETURN)
                  |}]
                |};
                {| EVMBlock.bid := 8%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Jump 9%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x01 ];
                      EVMInstruction.output := [ 23%nat ];
                      EVMInstruction.op := inr EVMInstruction.ASSIGN
                  |}]
                |}
             ];
             EVMFunction.entry_block_id := 0%nat
          |};
      {| EVMFunction.name := "function_modifier_sol__C__C_20__entry";
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
           EVMSmartContract.main := "function_modifier_sol__C__C_20__C_20_deployed__entry" 
       |}.

Definition liveness_info : FunctionName.t -> option EVMLiveness.fun_live_info_t :=
fun fname =>
   match fname with 
   | "function_modifier_sol__C__C_20__C_20_deployed__entry" => Some (
      fun blockid =>
         match blockid with 
         | 0%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [ 0%nat ])         
         | 2%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 1%nat => Some (EVMLiveness.list_to_set [ 0%nat ], EVMLiveness.list_to_set [ 0%nat ])         
         | 4%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 3%nat => Some (EVMLiveness.list_to_set [ 0%nat ], EVMLiveness.list_to_set [ 0%nat ])         
         | 6%nat => Some (EVMLiveness.list_to_set [ 0%nat ], EVMLiveness.list_to_set [ 18%nat; 0%nat ])         
         | 5%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 9%nat => Some (EVMLiveness.list_to_set [ 0%nat; 24%nat ], EVMLiveness.list_to_set [  ])         
         | 8%nat => Some (EVMLiveness.list_to_set [ 0%nat ], EVMLiveness.list_to_set [ 23%nat; 0%nat ])
         | _ => None
         end )
   | "function_modifier_sol__C__C_20__entry" => Some (
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
        