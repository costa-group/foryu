(* 
FORYU: Automatic translation for liveness analysis
Smart contract: malformed_panic_2.sol 
Date: 2025-11-24 23:48:01.543954

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


Module TestTranslation.

Definition sc_tr : EVMSmartContract.t :=
       {| EVMSmartContract.name := "malformed_panic_2.sol";
           EVMSmartContract.functions := [
      {| EVMFunction.name := "malformed_panic_2_sol__C__C_132__C_132_deployed__abi_decode";
             EVMFunction.arguments := [0%nat; 1%nat];
             EVMFunction.num_outputs := 0;
             EVMFunction.blocks := [
    
                {| EVMBlock.bid := 0%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 4%nat 2%nat 1%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inl 0%nat; inl 1%nat ];
                      EVMInstruction.output := [ 3%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SUB)
                  |};
                  {| EVMInstruction.input := [ inr 0x00; inl 3%nat ];
                      EVMInstruction.output := [ 4%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SLT)
                  |}]
                |};
                {| EVMBlock.bid := 2%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ReturnBlock [];
                   EVMBlock.instructions := [ 
    ]
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
          |};
      {| EVMFunction.name := "malformed_panic_2_sol__C__C_132__C_132_deployed__abi_decode_902";
             EVMFunction.arguments := [0%nat];
             EVMFunction.num_outputs := 0;
             EVMFunction.blocks := [
    
                {| EVMBlock.bid := 0%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 5%nat 2%nat 1%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x7f ];
                      EVMInstruction.output := [ 3%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.NOT)
                  |};
                  {| EVMInstruction.input := [ inl 3%nat; inl 0%nat ];
                      EVMInstruction.output := [ 4%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADD)
                  |};
                  {| EVMInstruction.input := [ inr 0x00; inl 4%nat ];
                      EVMInstruction.output := [ 5%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SLT)
                  |}]
                |};
                {| EVMBlock.bid := 2%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ReturnBlock [];
                   EVMBlock.instructions := [ 
    ]
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
          |};
      {| EVMFunction.name := "malformed_panic_2_sol__C__C_132__C_132_deployed__abi_encode_rational_by";
             EVMFunction.arguments := [0%nat];
             EVMFunction.num_outputs := 1;
             EVMFunction.blocks := [
    
                {| EVMBlock.bid := 0%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ReturnBlock [inl 3%nat];
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x20; inl 0%nat ];
                      EVMInstruction.output := [ 3%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADD)
                  |};
                  {| EVMInstruction.input := [ inr 0x06; inl 0%nat ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |}]
                |}
             ];
             EVMFunction.entry_block_id := 0%nat
          |};
      {| EVMFunction.name := "malformed_panic_2_sol__C__C_132__C_132_deployed__abi_encode_tuple_rational_by";
             EVMFunction.arguments := [0%nat];
             EVMFunction.num_outputs := 1;
             EVMFunction.blocks := [
    
                {| EVMBlock.bid := 0%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ReturnBlock [inl 3%nat];
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x20; inl 0%nat ];
                      EVMInstruction.output := [ 3%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADD)
                  |};
                  {| EVMInstruction.input := [ inr 0x03; inl 0%nat ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |}]
                |}
             ];
             EVMFunction.entry_block_id := 0%nat
          |};
      {| EVMFunction.name := "malformed_panic_2_sol__C__C_132__C_132_deployed__assert_helper";
             EVMFunction.arguments := [];
             EVMFunction.num_outputs := 0;
             EVMFunction.blocks := [
    
                {| EVMBlock.bid := 0%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x4e487b71; inr 0xe0 ];
                      EVMInstruction.output := [ 2%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SHL)
                  |};
                  {| EVMInstruction.input := [ inl 2%nat; inr 0x00 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |};
                  {| EVMInstruction.input := [ inr 0x01; inr 0x04 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |};
                  {| EVMInstruction.input := [ inr 0x24; inr 0x00 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.REVERT)
                  |}]
                |}
             ];
             EVMFunction.entry_block_id := 0%nat
          |};
      {| EVMFunction.name := "malformed_panic_2_sol__C__C_132__C_132_deployed__external_fun_b";
             EVMFunction.arguments := [];
             EVMFunction.num_outputs := 0;
             EVMFunction.blocks := [
    
                {| EVMBlock.bid := 0%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 0%nat 2%nat 1%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 0%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.CALLVALUE)
                  |}]
                |};
                {| EVMBlock.bid := 2%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 6%nat 5%nat 4%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x03 ];
                      EVMInstruction.output := [ 3%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.NOT)
                  |};
                  {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 4%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.CALLDATASIZE)
                  |};
                  {| EVMInstruction.input := [ inl 3%nat; inl 4%nat ];
                      EVMInstruction.output := [ 5%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADD)
                  |};
                  {| EVMInstruction.input := [ inr 0x00; inl 5%nat ];
                      EVMInstruction.output := [ 6%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SLT)
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
                |};
                {| EVMBlock.bid := 5%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 9%nat 8%nat 7%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 7%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADDRESS)
                  |};
                  {| EVMInstruction.input := [ inl 7%nat ];
                      EVMInstruction.output := [ 8%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.EXTCODESIZE)
                  |};
                  {| EVMInstruction.input := [ inl 8%nat ];
                      EVMInstruction.output := [ 9%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ISZERO)
                  |}]
                |};
                {| EVMBlock.bid := 4%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x00; inr 0x00 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.REVERT)
                  |}]
                |};
                {| EVMBlock.bid := 8%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 21%nat 11%nat 10%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x40 ];
                      EVMInstruction.output := [ 11%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.MLOAD)
                  |};
                  {| EVMInstruction.input := [ inr 0xb3de648b; inr 0xe0 ];
                      EVMInstruction.output := [ 14%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SHL)
                  |};
                  {| EVMInstruction.input := [ inl 14%nat; inl 11%nat ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |};
                  {| EVMInstruction.input := [ inr 0x04; inl 11%nat ];
                      EVMInstruction.output := [ 16%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADD)
                  |};
                  {| EVMInstruction.input := [ inl 16%nat ];
                      EVMInstruction.output := [ 17%nat ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__abi_encode_rational_by")
                  |};
                  {| EVMInstruction.input := [ inl 11%nat; inl 17%nat ];
                      EVMInstruction.output := [ 18%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SUB)
                  |};
                  {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 19%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADDRESS)
                  |};
                  {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 20%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.GAS)
                  |};
                  {| EVMInstruction.input := [ inr 0x00; inl 11%nat; inl 18%nat; inl 11%nat; inl 19%nat; inl 20%nat ];
                      EVMInstruction.output := [ 21%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.STATICCALL)
                  |}]
                |};
                {| EVMBlock.bid := 7%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x00; inr 0x00 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.REVERT)
                  |}]
                |};
                {| EVMBlock.bid := 11%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 24%nat 14%nat 13%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inl 21%nat ];
                      EVMInstruction.output := [ 23%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ISZERO)
                  |};
                  {| EVMInstruction.input := [ inr 0x00; inl 23%nat ];
                      EVMInstruction.output := [ 24%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.EQ)
                  |}]
                |};
                {| EVMBlock.bid := 10%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Jump 11%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x00; inl 11%nat ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__finalize_allocation")
                  |};
                  {| EVMInstruction.input := [ inl 11%nat; inl 11%nat ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__abi_decode")
                  |}]
                |};
                {| EVMBlock.bid := 14%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 29%nat 17%nat 16%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x01 ];
                      EVMInstruction.output := [ 26%nat ];
                      EVMInstruction.op := inr EVMInstruction.ASSIGN
                  |};
                  {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 27%nat ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__return_data_selector")
                  |};
                  {| EVMInstruction.input := [ inl 27%nat; inr 0x4e487b71 ];
                      EVMInstruction.output := [ 29%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.EQ)
                  |}]
                |};
                {| EVMBlock.bid := 13%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__assert_helper")
                  |}]
                |};
                {| EVMBlock.bid := 17%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 26%nat 22%nat 21%nat;
                   EVMBlock.instructions := [ 
    ]
                |};
                {| EVMBlock.bid := 16%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 30%nat 19%nat 18%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 30%nat; 31%nat ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__try_decode_panic_data")
                  |}]
                |};
                {| EVMBlock.bid := 22%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Jump 12%nat;
                   EVMBlock.instructions := [ 
    ]
                |};
                {| EVMBlock.bid := 21%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__revert_forward")
                  |}]
                |};
                {| EVMBlock.bid := 19%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Jump 17%nat;
                   EVMBlock.instructions := [ 
    ]
                |};
                {| EVMBlock.bid := 18%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x00 ];
                      EVMInstruction.output := [ 32%nat ];
                      EVMInstruction.op := inr EVMInstruction.ASSIGN
                  |};
                  {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__assert_helper")
                  |}]
                |};
                {| EVMBlock.bid := 12%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__assert_helper")
                  |}]
                |}
             ];
             EVMFunction.entry_block_id := 0%nat
          |};
      {| EVMFunction.name := "malformed_panic_2_sol__C__C_132__C_132_deployed__external_fun_c";
             EVMFunction.arguments := [];
             EVMFunction.num_outputs := 0;
             EVMFunction.blocks := [
    
                {| EVMBlock.bid := 0%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 0%nat 2%nat 1%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 0%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.CALLVALUE)
                  |}]
                |};
                {| EVMBlock.bid := 2%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 6%nat 5%nat 4%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x03 ];
                      EVMInstruction.output := [ 3%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.NOT)
                  |};
                  {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 4%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.CALLDATASIZE)
                  |};
                  {| EVMInstruction.input := [ inl 3%nat; inl 4%nat ];
                      EVMInstruction.output := [ 5%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADD)
                  |};
                  {| EVMInstruction.input := [ inr 0x00; inl 5%nat ];
                      EVMInstruction.output := [ 6%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SLT)
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
                |};
                {| EVMBlock.bid := 5%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 7%nat ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__fun_c")
                  |};
                  {| EVMInstruction.input := [ inr 0x40 ];
                      EVMInstruction.output := [ 9%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.MLOAD)
                  |};
                  {| EVMInstruction.input := [ inl 7%nat; inl 9%nat ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |};
                  {| EVMInstruction.input := [ inr 0x20; inl 9%nat ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.RETURN)
                  |}]
                |};
                {| EVMBlock.bid := 4%nat;
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
      {| EVMFunction.name := "malformed_panic_2_sol__C__C_132__C_132_deployed__external_fun_d";
             EVMFunction.arguments := [];
             EVMFunction.num_outputs := 0;
             EVMFunction.blocks := [
    
                {| EVMBlock.bid := 0%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 0%nat 2%nat 1%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 0%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.CALLVALUE)
                  |}]
                |};
                {| EVMBlock.bid := 2%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 6%nat 5%nat 4%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x03 ];
                      EVMInstruction.output := [ 3%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.NOT)
                  |};
                  {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 4%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.CALLDATASIZE)
                  |};
                  {| EVMInstruction.input := [ inl 3%nat; inl 4%nat ];
                      EVMInstruction.output := [ 5%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADD)
                  |};
                  {| EVMInstruction.input := [ inr 0x00; inl 5%nat ];
                      EVMInstruction.output := [ 6%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SLT)
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
                |};
                {| EVMBlock.bid := 5%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 7%nat ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__fun_d")
                  |};
                  {| EVMInstruction.input := [ inr 0x40 ];
                      EVMInstruction.output := [ 9%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.MLOAD)
                  |};
                  {| EVMInstruction.input := [ inl 7%nat; inl 9%nat ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |};
                  {| EVMInstruction.input := [ inr 0x20; inl 9%nat ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.RETURN)
                  |}]
                |};
                {| EVMBlock.bid := 4%nat;
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
      {| EVMFunction.name := "malformed_panic_2_sol__C__C_132__C_132_deployed__external_fun_f";
             EVMFunction.arguments := [];
             EVMFunction.num_outputs := 0;
             EVMFunction.blocks := [
    
                {| EVMBlock.bid := 0%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 0%nat 2%nat 1%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 0%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.CALLVALUE)
                  |}]
                |};
                {| EVMBlock.bid := 2%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 7%nat 5%nat 4%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x03 ];
                      EVMInstruction.output := [ 4%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.NOT)
                  |};
                  {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 5%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.CALLDATASIZE)
                  |};
                  {| EVMInstruction.input := [ inl 4%nat; inl 5%nat ];
                      EVMInstruction.output := [ 6%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADD)
                  |};
                  {| EVMInstruction.input := [ inr 0x20; inl 6%nat ];
                      EVMInstruction.output := [ 7%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SLT)
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
                |};
                {| EVMBlock.bid := 5%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x4e487b71; inr 0xe0 ];
                      EVMInstruction.output := [ 10%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SHL)
                  |};
                  {| EVMInstruction.input := [ inl 10%nat; inr 0x00 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |};
                  {| EVMInstruction.input := [ inr 0x43; inr 0x04 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |};
                  {| EVMInstruction.input := [ inr 0x04 ];
                      EVMInstruction.output := [ 13%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.CALLDATALOAD)
                  |};
                  {| EVMInstruction.input := [ inl 13%nat; inr 0x00 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.REVERT)
                  |}]
                |};
                {| EVMBlock.bid := 4%nat;
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
      {| EVMFunction.name := "malformed_panic_2_sol__C__C_132__C_132_deployed__finalize_allocation";
             EVMFunction.arguments := [0%nat; 1%nat];
             EVMFunction.num_outputs := 0;
             EVMFunction.blocks := [
    
                {| EVMBlock.bid := 0%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 10%nat 2%nat 1%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x1f ];
                      EVMInstruction.output := [ 3%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.NOT)
                  |};
                  {| EVMInstruction.input := [ inr 0x1f; inl 1%nat ];
                      EVMInstruction.output := [ 4%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADD)
                  |};
                  {| EVMInstruction.input := [ inl 3%nat; inl 4%nat ];
                      EVMInstruction.output := [ 5%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.AND)
                  |};
                  {| EVMInstruction.input := [ inl 5%nat; inl 0%nat ];
                      EVMInstruction.output := [ 6%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADD)
                  |};
                  {| EVMInstruction.input := [ inl 0%nat; inl 6%nat ];
                      EVMInstruction.output := [ 7%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.LT)
                  |};
                  {| EVMInstruction.input := [ inr 0xffffffffffffffff; inl 6%nat ];
                      EVMInstruction.output := [ 9%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.GT)
                  |};
                  {| EVMInstruction.input := [ inl 7%nat; inl 9%nat ];
                      EVMInstruction.output := [ 10%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.OR)
                  |}]
                |};
                {| EVMBlock.bid := 2%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ReturnBlock [];
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inl 6%nat; inr 0x40 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |}]
                |};
                {| EVMBlock.bid := 1%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x4e487b71; inr 0xe0 ];
                      EVMInstruction.output := [ 13%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SHL)
                  |};
                  {| EVMInstruction.input := [ inl 13%nat; inr 0x00 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |};
                  {| EVMInstruction.input := [ inr 0x41; inr 0x04 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |};
                  {| EVMInstruction.input := [ inr 0x24; inr 0x00 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.REVERT)
                  |}]
                |}
             ];
             EVMFunction.entry_block_id := 0%nat
          |};
      {| EVMFunction.name := "malformed_panic_2_sol__C__C_132__C_132_deployed__finalize_allocation_901";
             EVMFunction.arguments := [0%nat];
             EVMFunction.num_outputs := 0;
             EVMFunction.blocks := [
    
                {| EVMBlock.bid := 0%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 10%nat 2%nat 1%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x1f ];
                      EVMInstruction.output := [ 2%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.NOT)
                  |};
                  {| EVMInstruction.input := [ inr 0x1f; inl 0%nat ];
                      EVMInstruction.output := [ 3%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADD)
                  |};
                  {| EVMInstruction.input := [ inl 2%nat; inl 3%nat ];
                      EVMInstruction.output := [ 4%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.AND)
                  |};
                  {| EVMInstruction.input := [ inl 4%nat; inr 0x80 ];
                      EVMInstruction.output := [ 6%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADD)
                  |};
                  {| EVMInstruction.input := [ inr 0x80; inl 6%nat ];
                      EVMInstruction.output := [ 7%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.LT)
                  |};
                  {| EVMInstruction.input := [ inr 0xffffffffffffffff; inl 6%nat ];
                      EVMInstruction.output := [ 9%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.GT)
                  |};
                  {| EVMInstruction.input := [ inl 7%nat; inl 9%nat ];
                      EVMInstruction.output := [ 10%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.OR)
                  |}]
                |};
                {| EVMBlock.bid := 2%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ReturnBlock [];
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inl 6%nat; inr 0x40 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |}]
                |};
                {| EVMBlock.bid := 1%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x4e487b71; inr 0xe0 ];
                      EVMInstruction.output := [ 13%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SHL)
                  |};
                  {| EVMInstruction.input := [ inl 13%nat; inr 0x00 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |};
                  {| EVMInstruction.input := [ inr 0x41; inr 0x04 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |};
                  {| EVMInstruction.input := [ inr 0x24; inr 0x00 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.REVERT)
                  |}]
                |}
             ];
             EVMFunction.entry_block_id := 0%nat
          |};
      {| EVMFunction.name := "malformed_panic_2_sol__C__C_132__C_132_deployed__fun_c";
             EVMFunction.arguments := [];
             EVMFunction.num_outputs := 1;
             EVMFunction.blocks := [
    
                {| EVMBlock.bid := 0%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 4%nat 2%nat 1%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x00 ];
                      EVMInstruction.output := [ 1%nat ];
                      EVMInstruction.op := inr EVMInstruction.ASSIGN
                  |};
                  {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 2%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADDRESS)
                  |};
                  {| EVMInstruction.input := [ inl 2%nat ];
                      EVMInstruction.output := [ 3%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.EXTCODESIZE)
                  |};
                  {| EVMInstruction.input := [ inl 3%nat ];
                      EVMInstruction.output := [ 4%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ISZERO)
                  |}]
                |};
                {| EVMBlock.bid := 2%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 17%nat 5%nat 4%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x40 ];
                      EVMInstruction.output := [ 6%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.MLOAD)
                  |};
                  {| EVMInstruction.input := [ inr 0xb3de648b; inr 0xe0 ];
                      EVMInstruction.output := [ 9%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SHL)
                  |};
                  {| EVMInstruction.input := [ inl 9%nat; inl 6%nat ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |};
                  {| EVMInstruction.input := [ inr 0x00 ];
                      EVMInstruction.output := [ 10%nat ];
                      EVMInstruction.op := inr EVMInstruction.ASSIGN
                  |};
                  {| EVMInstruction.input := [ inr 0x24; inl 6%nat ];
                      EVMInstruction.output := [ 12%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADD)
                  |};
                  {| EVMInstruction.input := [ inr 0x04; inl 6%nat ];
                      EVMInstruction.output := [ 14%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADD)
                  |};
                  {| EVMInstruction.input := [ inr 0x24; inl 14%nat ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |};
                  {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 15%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADDRESS)
                  |};
                  {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 16%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.GAS)
                  |};
                  {| EVMInstruction.input := [ inr 0x00; inl 6%nat; inr 0x24; inl 6%nat; inl 15%nat; inl 16%nat ];
                      EVMInstruction.output := [ 17%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.STATICCALL)
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
                |};
                {| EVMBlock.bid := 5%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 25%nat 11%nat 10%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inl 17%nat ];
                      EVMInstruction.output := [ 24%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ISZERO)
                  |};
                  {| EVMInstruction.input := [ inr 0x00; inl 24%nat ];
                      EVMInstruction.output := [ 25%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.EQ)
                  |}]
                |};
                {| EVMBlock.bid := 4%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 19%nat 7%nat 6%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x00; inl 6%nat ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__finalize_allocation")
                  |};
                  {| EVMInstruction.input := [ inl 6%nat; inl 6%nat ];
                      EVMInstruction.output := [ 18%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SUB)
                  |};
                  {| EVMInstruction.input := [ inr 0x00; inl 18%nat ];
                      EVMInstruction.output := [ 19%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SLT)
                  |}]
                |};
                {| EVMBlock.bid := 11%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 28%nat 14%nat 13%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 26%nat ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__return_data_selector")
                  |};
                  {| EVMInstruction.input := [ inl 26%nat; inr 0x4e487b71 ];
                      EVMInstruction.output := [ 28%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.EQ)
                  |}]
                |};
                {| EVMBlock.bid := 10%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__assert_helper")
                  |}]
                |};
                {| EVMBlock.bid := 7%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Jump 5%nat;
                   EVMBlock.instructions := [ 
    ]
                |};
                {| EVMBlock.bid := 6%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x00; inr 0x00 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.REVERT)
                  |}]
                |};
                {| EVMBlock.bid := 14%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__revert_forward")
                  |}]
                |};
                {| EVMBlock.bid := 13%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 29%nat 16%nat 15%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 29%nat; 30%nat ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__try_decode_panic_data")
                  |}]
                |};
                {| EVMBlock.bid := 16%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Jump 14%nat;
                   EVMBlock.instructions := [ 
    ]
                |};
                {| EVMBlock.bid := 15%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ReturnBlock [inl 30%nat];
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x00 ];
                      EVMInstruction.output := [ 31%nat ];
                      EVMInstruction.op := inr EVMInstruction.ASSIGN
                  |};
                  {| EVMInstruction.input := [ inr 0x00 ];
                      EVMInstruction.output := [ 32%nat ];
                      EVMInstruction.op := inr EVMInstruction.ASSIGN
                  |}]
                |}
             ];
             EVMFunction.entry_block_id := 0%nat
          |};
      {| EVMFunction.name := "malformed_panic_2_sol__C__C_132__C_132_deployed__fun_d";
             EVMFunction.arguments := [];
             EVMFunction.num_outputs := 1;
             EVMFunction.blocks := [
    
                {| EVMBlock.bid := 0%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 4%nat 2%nat 1%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x00 ];
                      EVMInstruction.output := [ 1%nat ];
                      EVMInstruction.op := inr EVMInstruction.ASSIGN
                  |};
                  {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 2%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADDRESS)
                  |};
                  {| EVMInstruction.input := [ inl 2%nat ];
                      EVMInstruction.output := [ 3%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.EXTCODESIZE)
                  |};
                  {| EVMInstruction.input := [ inl 3%nat ];
                      EVMInstruction.output := [ 4%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ISZERO)
                  |}]
                |};
                {| EVMBlock.bid := 2%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 18%nat 5%nat 4%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x40 ];
                      EVMInstruction.output := [ 6%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.MLOAD)
                  |};
                  {| EVMInstruction.input := [ inr 0xb3de648b; inr 0xe0 ];
                      EVMInstruction.output := [ 9%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SHL)
                  |};
                  {| EVMInstruction.input := [ inl 9%nat; inl 6%nat ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |};
                  {| EVMInstruction.input := [ inr 0x00 ];
                      EVMInstruction.output := [ 10%nat ];
                      EVMInstruction.op := inr EVMInstruction.ASSIGN
                  |};
                  {| EVMInstruction.input := [ inr 0x24; inl 6%nat ];
                      EVMInstruction.output := [ 12%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADD)
                  |};
                  {| EVMInstruction.input := [ inr 0x04; inl 6%nat ];
                      EVMInstruction.output := [ 15%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADD)
                  |};
                  {| EVMInstruction.input := [ inr 0x0100; inl 15%nat ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |};
                  {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 16%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADDRESS)
                  |};
                  {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 17%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.GAS)
                  |};
                  {| EVMInstruction.input := [ inr 0x00; inl 6%nat; inr 0x24; inl 6%nat; inl 16%nat; inl 17%nat ];
                      EVMInstruction.output := [ 18%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.STATICCALL)
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
                |};
                {| EVMBlock.bid := 5%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 26%nat 11%nat 10%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inl 18%nat ];
                      EVMInstruction.output := [ 25%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ISZERO)
                  |};
                  {| EVMInstruction.input := [ inr 0x00; inl 25%nat ];
                      EVMInstruction.output := [ 26%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.EQ)
                  |}]
                |};
                {| EVMBlock.bid := 4%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 20%nat 7%nat 6%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x00; inl 6%nat ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__finalize_allocation")
                  |};
                  {| EVMInstruction.input := [ inl 6%nat; inl 6%nat ];
                      EVMInstruction.output := [ 19%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SUB)
                  |};
                  {| EVMInstruction.input := [ inr 0x00; inl 19%nat ];
                      EVMInstruction.output := [ 20%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SLT)
                  |}]
                |};
                {| EVMBlock.bid := 11%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 29%nat 14%nat 13%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 27%nat ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__return_data_selector")
                  |};
                  {| EVMInstruction.input := [ inl 27%nat; inr 0x4e487b71 ];
                      EVMInstruction.output := [ 29%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.EQ)
                  |}]
                |};
                {| EVMBlock.bid := 10%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__assert_helper")
                  |}]
                |};
                {| EVMBlock.bid := 7%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Jump 5%nat;
                   EVMBlock.instructions := [ 
    ]
                |};
                {| EVMBlock.bid := 6%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x00; inr 0x00 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.REVERT)
                  |}]
                |};
                {| EVMBlock.bid := 14%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__revert_forward")
                  |}]
                |};
                {| EVMBlock.bid := 13%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 30%nat 16%nat 15%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 30%nat; 31%nat ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__try_decode_panic_data")
                  |}]
                |};
                {| EVMBlock.bid := 16%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Jump 14%nat;
                   EVMBlock.instructions := [ 
    ]
                |};
                {| EVMBlock.bid := 15%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ReturnBlock [inl 31%nat];
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x00 ];
                      EVMInstruction.output := [ 32%nat ];
                      EVMInstruction.op := inr EVMInstruction.ASSIGN
                  |};
                  {| EVMInstruction.input := [ inr 0x00 ];
                      EVMInstruction.output := [ 33%nat ];
                      EVMInstruction.op := inr EVMInstruction.ASSIGN
                  |}]
                |}
             ];
             EVMFunction.entry_block_id := 0%nat
          |};
      {| EVMFunction.name := "malformed_panic_2_sol__C__C_132__C_132_deployed__return_data_selector";
             EVMFunction.arguments := [];
             EVMFunction.num_outputs := 1;
             EVMFunction.blocks := [
    
                {| EVMBlock.bid := 0%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 3%nat 2%nat 1%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 2%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.RETURNDATASIZE)
                  |};
                  {| EVMInstruction.input := [ inr 0x03; inl 2%nat ];
                      EVMInstruction.output := [ 3%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.GT)
                  |}]
                |};
                {| EVMBlock.bid := 2%nat;
                   EVMBlock.phi_function := fun blockid => if BlockID.eqb blockid 0%nat then [(8%nat, inr 0x00)] else if BlockID.eqb blockid 1%nat then [(8%nat, inl 7%nat)] else [];
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ReturnBlock [inl 8%nat];
                   EVMBlock.instructions := [ 
    ]
                |};
                {| EVMBlock.bid := 1%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Jump 2%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x04; inr 0x00; inr 0x00 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.RETURNDATACOPY)
                  |};
                  {| EVMInstruction.input := [ inr 0x00 ];
                      EVMInstruction.output := [ 5%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.MLOAD)
                  |};
                  {| EVMInstruction.input := [ inl 5%nat; inr 0xe0 ];
                      EVMInstruction.output := [ 7%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SHR)
                  |}]
                |}
             ];
             EVMFunction.entry_block_id := 0%nat
          |};
      {| EVMFunction.name := "malformed_panic_2_sol__C__C_132__C_132_deployed__revert_forward";
             EVMFunction.arguments := [];
             EVMFunction.num_outputs := 0;
             EVMFunction.blocks := [
    
                {| EVMBlock.bid := 0%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x40 ];
                      EVMInstruction.output := [ 1%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.MLOAD)
                  |};
                  {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 2%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.RETURNDATASIZE)
                  |};
                  {| EVMInstruction.input := [ inl 2%nat; inr 0x00; inl 1%nat ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.RETURNDATACOPY)
                  |};
                  {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 4%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.RETURNDATASIZE)
                  |};
                  {| EVMInstruction.input := [ inl 4%nat; inl 1%nat ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.REVERT)
                  |}]
                |}
             ];
             EVMFunction.entry_block_id := 0%nat
          |};
      {| EVMFunction.name := "malformed_panic_2_sol__C__C_132__C_132_deployed__try_decode_panic_data";
             EVMFunction.arguments := [];
             EVMFunction.num_outputs := 2;
             EVMFunction.blocks := [
    
                {| EVMBlock.bid := 0%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 3%nat 2%nat 1%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 2%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.RETURNDATASIZE)
                  |};
                  {| EVMInstruction.input := [ inr 0x23; inl 2%nat ];
                      EVMInstruction.output := [ 3%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.GT)
                  |}]
                |};
                {| EVMBlock.bid := 2%nat;
                   EVMBlock.phi_function := fun blockid => if BlockID.eqb blockid 0%nat then [(9%nat, inr 0x00); (10%nat, inr 0x00)] else if BlockID.eqb blockid 1%nat then [(9%nat, inl 7%nat); (10%nat, inl 8%nat)] else [];
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ReturnBlock [inl 9%nat; inl 10%nat];
                   EVMBlock.instructions := [ 
    ]
                |};
                {| EVMBlock.bid := 1%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Jump 2%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x20; inr 0x04; inr 0x00 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.RETURNDATACOPY)
                  |};
                  {| EVMInstruction.input := [ inr 0x01 ];
                      EVMInstruction.output := [ 7%nat ];
                      EVMInstruction.op := inr EVMInstruction.ASSIGN
                  |};
                  {| EVMInstruction.input := [ inr 0x00 ];
                      EVMInstruction.output := [ 8%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.MLOAD)
                  |}]
                |}
             ];
             EVMFunction.entry_block_id := 0%nat
          |};
      {| EVMFunction.name := "malformed_panic_2_sol__C__C_132__C_132_deployed__entry";
             EVMFunction.arguments := [];
             EVMFunction.num_outputs := 0;
             EVMFunction.blocks := [
    
                {| EVMBlock.bid := 0%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 5%nat 2%nat 1%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x80; inr 0x40 ];
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
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 10%nat 5%nat 4%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x00 ];
                      EVMInstruction.output := [ 7%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.CALLDATALOAD)
                  |};
                  {| EVMInstruction.input := [ inl 7%nat; inr 0xe0 ];
                      EVMInstruction.output := [ 9%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SHR)
                  |};
                  {| EVMInstruction.input := [ inr 0x0dbe671f; inl 9%nat ];
                      EVMInstruction.output := [ 10%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.EQ)
                  |}]
                |};
                {| EVMBlock.bid := 5%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 46%nat 31%nat 30%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x4df7e3d0; inl 9%nat ];
                      EVMInstruction.output := [ 46%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.EQ)
                  |}]
                |};
                {| EVMBlock.bid := 4%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 12%nat 7%nat 6%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 12%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.CALLVALUE)
                  |}]
                |};
                {| EVMBlock.bid := 31%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 48%nat 34%nat 33%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x8a054ac2; inl 9%nat ];
                      EVMInstruction.output := [ 48%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.EQ)
                  |}]
                |};
                {| EVMBlock.bid := 30%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__external_fun_b")
                  |}]
                |};
                {| EVMBlock.bid := 7%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 17%nat 10%nat 9%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x03 ];
                      EVMInstruction.output := [ 14%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.NOT)
                  |};
                  {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 15%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.CALLDATASIZE)
                  |};
                  {| EVMInstruction.input := [ inl 14%nat; inl 15%nat ];
                      EVMInstruction.output := [ 16%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADD)
                  |};
                  {| EVMInstruction.input := [ inr 0x00; inl 16%nat ];
                      EVMInstruction.output := [ 17%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SLT)
                  |}]
                |};
                {| EVMBlock.bid := 6%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x00; inr 0x00 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.REVERT)
                  |}]
                |};
                {| EVMBlock.bid := 34%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 50%nat 37%nat 36%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0xb3de648b; inl 9%nat ];
                      EVMInstruction.output := [ 50%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.EQ)
                  |}]
                |};
                {| EVMBlock.bid := 33%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__external_fun_d")
                  |}]
                |};
                {| EVMBlock.bid := 10%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 20%nat 13%nat 12%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 18%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADDRESS)
                  |};
                  {| EVMInstruction.input := [ inl 18%nat ];
                      EVMInstruction.output := [ 19%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.EXTCODESIZE)
                  |};
                  {| EVMInstruction.input := [ inl 19%nat ];
                      EVMInstruction.output := [ 20%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ISZERO)
                  |}]
                |};
                {| EVMBlock.bid := 9%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x00; inr 0x00 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.REVERT)
                  |}]
                |};
                {| EVMBlock.bid := 37%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 51%nat 3%nat 39%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0xc3da42b8; inl 9%nat ];
                      EVMInstruction.output := [ 51%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.EQ)
                  |}]
                |};
                {| EVMBlock.bid := 36%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__external_fun_f")
                  |}]
                |};
                {| EVMBlock.bid := 13%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 30%nat 16%nat 15%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0xb3de648b; inr 0xe0 ];
                      EVMInstruction.output := [ 22%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SHL)
                  |};
                  {| EVMInstruction.input := [ inl 22%nat; inr 0x80 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |};
                  {| EVMInstruction.input := [ inr 0x7f ];
                      EVMInstruction.output := [ 24%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.NOT)
                  |};
                  {| EVMInstruction.input := [ inr 0x84 ];
                      EVMInstruction.output := [ 26%nat ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__abi_encode_tuple_rational_by")
                  |};
                  {| EVMInstruction.input := [ inl 24%nat; inl 26%nat ];
                      EVMInstruction.output := [ 27%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADD)
                  |};
                  {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 28%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADDRESS)
                  |};
                  {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 29%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.GAS)
                  |};
                  {| EVMInstruction.input := [ inr 0x00; inr 0x80; inl 27%nat; inr 0x80; inl 28%nat; inl 29%nat ];
                      EVMInstruction.output := [ 30%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.STATICCALL)
                  |}]
                |};
                {| EVMBlock.bid := 12%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x00; inr 0x00 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.REVERT)
                  |}]
                |};
                {| EVMBlock.bid := 3%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Jump 2%nat;
                   EVMBlock.instructions := [ 
    ]
                |};
                {| EVMBlock.bid := 39%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__external_fun_c")
                  |}]
                |};
                {| EVMBlock.bid := 16%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 33%nat 19%nat 18%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inl 30%nat ];
                      EVMInstruction.output := [ 32%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ISZERO)
                  |};
                  {| EVMInstruction.input := [ inr 0x00; inl 32%nat ];
                      EVMInstruction.output := [ 33%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.EQ)
                  |}]
                |};
                {| EVMBlock.bid := 15%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Jump 16%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x00 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__finalize_allocation_901")
                  |};
                  {| EVMInstruction.input := [ inr 0x80 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__abi_decode_902")
                  |}]
                |};
                {| EVMBlock.bid := 19%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 38%nat 22%nat 21%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x01 ];
                      EVMInstruction.output := [ 35%nat ];
                      EVMInstruction.op := inr EVMInstruction.ASSIGN
                  |};
                  {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 36%nat ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__return_data_selector")
                  |};
                  {| EVMInstruction.input := [ inl 36%nat; inr 0x4e487b71 ];
                      EVMInstruction.output := [ 38%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.EQ)
                  |}]
                |};
                {| EVMBlock.bid := 18%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__assert_helper")
                  |}]
                |};
                {| EVMBlock.bid := 22%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 35%nat 27%nat 26%nat;
                   EVMBlock.instructions := [ 
    ]
                |};
                {| EVMBlock.bid := 21%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 39%nat 24%nat 23%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 39%nat; 40%nat ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__try_decode_panic_data")
                  |}]
                |};
                {| EVMBlock.bid := 27%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Jump 17%nat;
                   EVMBlock.instructions := [ 
    ]
                |};
                {| EVMBlock.bid := 26%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__revert_forward")
                  |}]
                |};
                {| EVMBlock.bid := 24%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Jump 22%nat;
                   EVMBlock.instructions := [ 
    ]
                |};
                {| EVMBlock.bid := 23%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x00 ];
                      EVMInstruction.output := [ 41%nat ];
                      EVMInstruction.op := inr EVMInstruction.ASSIGN
                  |};
                  {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__assert_helper")
                  |}]
                |};
                {| EVMBlock.bid := 17%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inl "malformed_panic_2_sol__C__C_132__C_132_deployed__assert_helper")
                  |}]
                |}
             ];
             EVMFunction.entry_block_id := 0%nat
          |};
      {| EVMFunction.name := "malformed_panic_2_sol__C__C_132__entry";
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
           EVMSmartContract.main := "malformed_panic_2_sol__C__C_132__C_132_deployed__abi_decode" 
       |}.

Definition liveness_info : FunctionName.t -> option EVMLiveness.fun_live_info_t :=
fun fname =>
   match fname with 
   | "malformed_panic_2_sol__C__C_132__C_132_deployed__abi_decode" => Some (
      fun blockid =>
         match blockid with 
         | 0%nat => Some (EVMLiveness.list_to_set [ 0%nat; 1%nat ], EVMLiveness.list_to_set [  ])         
         | 2%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 1%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])
         | _ => None
         end )
   | "malformed_panic_2_sol__C__C_132__C_132_deployed__abi_decode_902" => Some (
      fun blockid =>
         match blockid with 
         | 0%nat => Some (EVMLiveness.list_to_set [ 0%nat ], EVMLiveness.list_to_set [  ])         
         | 2%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 1%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])
         | _ => None
         end )
   | "malformed_panic_2_sol__C__C_132__C_132_deployed__abi_encode_rational_by" => Some (
      fun blockid =>
         match blockid with 
         | 0%nat => Some (EVMLiveness.list_to_set [ 0%nat ], EVMLiveness.list_to_set [ 3%nat ])
         | _ => None
         end )
   | "malformed_panic_2_sol__C__C_132__C_132_deployed__abi_encode_tuple_rational_by" => Some (
      fun blockid =>
         match blockid with 
         | 0%nat => Some (EVMLiveness.list_to_set [ 0%nat ], EVMLiveness.list_to_set [ 3%nat ])
         | _ => None
         end )
   | "malformed_panic_2_sol__C__C_132__C_132_deployed__assert_helper" => Some (
      fun blockid =>
         match blockid with 
         | 0%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])
         | _ => None
         end )
   | "malformed_panic_2_sol__C__C_132__C_132_deployed__external_fun_b" => Some (
      fun blockid =>
         match blockid with 
         | 0%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 2%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 1%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 5%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 4%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 8%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [ 21%nat; 11%nat ])         
         | 7%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 11%nat => Some (EVMLiveness.list_to_set [ 21%nat ], EVMLiveness.list_to_set [  ])         
         | 10%nat => Some (EVMLiveness.list_to_set [ 21%nat; 11%nat ], EVMLiveness.list_to_set [ 21%nat ])         
         | 14%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [ 26%nat ])         
         | 13%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 17%nat => Some (EVMLiveness.list_to_set [ 26%nat ], EVMLiveness.list_to_set [  ])         
         | 16%nat => Some (EVMLiveness.list_to_set [ 26%nat ], EVMLiveness.list_to_set [ 26%nat ])         
         | 22%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 21%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 19%nat => Some (EVMLiveness.list_to_set [ 26%nat ], EVMLiveness.list_to_set [ 26%nat ])         
         | 18%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 12%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])
         | _ => None
         end )
   | "malformed_panic_2_sol__C__C_132__C_132_deployed__external_fun_c" => Some (
      fun blockid =>
         match blockid with 
         | 0%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 2%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 1%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 5%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 4%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])
         | _ => None
         end )
   | "malformed_panic_2_sol__C__C_132__C_132_deployed__external_fun_d" => Some (
      fun blockid =>
         match blockid with 
         | 0%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 2%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 1%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 5%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 4%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])
         | _ => None
         end )
   | "malformed_panic_2_sol__C__C_132__C_132_deployed__external_fun_f" => Some (
      fun blockid =>
         match blockid with 
         | 0%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 2%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 1%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 5%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 4%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])
         | _ => None
         end )
   | "malformed_panic_2_sol__C__C_132__C_132_deployed__finalize_allocation" => Some (
      fun blockid =>
         match blockid with 
         | 0%nat => Some (EVMLiveness.list_to_set [ 0%nat; 1%nat ], EVMLiveness.list_to_set [ 6%nat ])         
         | 2%nat => Some (EVMLiveness.list_to_set [ 6%nat ], EVMLiveness.list_to_set [  ])         
         | 1%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])
         | _ => None
         end )
   | "malformed_panic_2_sol__C__C_132__C_132_deployed__finalize_allocation_901" => Some (
      fun blockid =>
         match blockid with 
         | 0%nat => Some (EVMLiveness.list_to_set [ 0%nat ], EVMLiveness.list_to_set [ 6%nat ])         
         | 2%nat => Some (EVMLiveness.list_to_set [ 6%nat ], EVMLiveness.list_to_set [  ])         
         | 1%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])
         | _ => None
         end )
   | "malformed_panic_2_sol__C__C_132__C_132_deployed__fun_c" => Some (
      fun blockid =>
         match blockid with 
         | 0%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 2%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [ 17%nat; 6%nat ])         
         | 1%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 5%nat => Some (EVMLiveness.list_to_set [ 17%nat ], EVMLiveness.list_to_set [  ])         
         | 4%nat => Some (EVMLiveness.list_to_set [ 17%nat; 6%nat ], EVMLiveness.list_to_set [ 17%nat ])         
         | 11%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 10%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 7%nat => Some (EVMLiveness.list_to_set [ 17%nat ], EVMLiveness.list_to_set [ 17%nat ])         
         | 6%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 14%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 13%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [ 30%nat ])         
         | 16%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 15%nat => Some (EVMLiveness.list_to_set [ 30%nat ], EVMLiveness.list_to_set [ 30%nat ])
         | _ => None
         end )
   | "malformed_panic_2_sol__C__C_132__C_132_deployed__fun_d" => Some (
      fun blockid =>
         match blockid with 
         | 0%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 2%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [ 18%nat; 6%nat ])         
         | 1%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 5%nat => Some (EVMLiveness.list_to_set [ 18%nat ], EVMLiveness.list_to_set [  ])         
         | 4%nat => Some (EVMLiveness.list_to_set [ 18%nat; 6%nat ], EVMLiveness.list_to_set [ 18%nat ])         
         | 11%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 10%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 7%nat => Some (EVMLiveness.list_to_set [ 18%nat ], EVMLiveness.list_to_set [ 18%nat ])         
         | 6%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 14%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 13%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [ 31%nat ])         
         | 16%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 15%nat => Some (EVMLiveness.list_to_set [ 31%nat ], EVMLiveness.list_to_set [ 31%nat ])
         | _ => None
         end )
   | "malformed_panic_2_sol__C__C_132__C_132_deployed__return_data_selector" => Some (
      fun blockid =>
         match blockid with 
         | 0%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 2%nat => Some (EVMLiveness.list_to_set [ 8%nat ], EVMLiveness.list_to_set [ 8%nat ])         
         | 1%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [ 7%nat ])
         | _ => None
         end )
   | "malformed_panic_2_sol__C__C_132__C_132_deployed__revert_forward" => Some (
      fun blockid =>
         match blockid with 
         | 0%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])
         | _ => None
         end )
   | "malformed_panic_2_sol__C__C_132__C_132_deployed__try_decode_panic_data" => Some (
      fun blockid =>
         match blockid with 
         | 0%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 2%nat => Some (EVMLiveness.list_to_set [ 9%nat; 10%nat ], EVMLiveness.list_to_set [ 9%nat; 10%nat ])         
         | 1%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [ 7%nat; 8%nat ])
         | _ => None
         end )
   | "malformed_panic_2_sol__C__C_132__C_132_deployed__entry" => Some (
      fun blockid =>
         match blockid with 
         | 0%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 2%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 1%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [ 9%nat ])         
         | 5%nat => Some (EVMLiveness.list_to_set [ 9%nat ], EVMLiveness.list_to_set [ 9%nat ])         
         | 4%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 31%nat => Some (EVMLiveness.list_to_set [ 9%nat ], EVMLiveness.list_to_set [ 9%nat ])         
         | 30%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 7%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 6%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 34%nat => Some (EVMLiveness.list_to_set [ 9%nat ], EVMLiveness.list_to_set [ 9%nat ])         
         | 33%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 10%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 9%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 37%nat => Some (EVMLiveness.list_to_set [ 9%nat ], EVMLiveness.list_to_set [  ])         
         | 36%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 13%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [ 30%nat ])         
         | 12%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 3%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 39%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 16%nat => Some (EVMLiveness.list_to_set [ 30%nat ], EVMLiveness.list_to_set [  ])         
         | 15%nat => Some (EVMLiveness.list_to_set [ 30%nat ], EVMLiveness.list_to_set [ 30%nat ])         
         | 19%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [ 35%nat ])         
         | 18%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 22%nat => Some (EVMLiveness.list_to_set [ 35%nat ], EVMLiveness.list_to_set [  ])         
         | 21%nat => Some (EVMLiveness.list_to_set [ 35%nat ], EVMLiveness.list_to_set [ 35%nat ])         
         | 27%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 26%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 24%nat => Some (EVMLiveness.list_to_set [ 35%nat ], EVMLiveness.list_to_set [ 35%nat ])         
         | 23%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 17%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])
         | _ => None
         end )
   | "malformed_panic_2_sol__C__C_132__entry" => Some (
      fun blockid =>
         match blockid with 
         | 0%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [ 0%nat ])         
         | 2%nat => Some (EVMLiveness.list_to_set [ 0%nat ], EVMLiveness.list_to_set [  ])         
         | 1%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])
         | _ => None
         end )
   | _ => None
   end.

Definition check := EVMLiveness.check_smart_contract_subset sc_tr liveness_info.   

(* Launches liveness check *)
Compute (check).

End TestTranslation.
        