(* 
FORYU: Automatic translation for liveness analysis
Smart contract: array_copy_storage_to_memory.sol 
Date: 2025-11-24 20:25:38.012725

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
       {| EVMSmartContract.name := "array_copy_storage_to_memory.sol";
           EVMSmartContract.functions := [
      {| EVMFunction.name := "array_copy_storage_to_memory_sol__C__C_44__C_44_deployed__array_push_from_uint256_to_array_uint256_dyn_storage_ptr";
             EVMFunction.arguments := [];
             EVMFunction.num_outputs := 0;
             EVMFunction.blocks := [
    
                {| EVMBlock.bid := 0%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 4%nat 2%nat 1%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x00 ];
                      EVMInstruction.output := [ 1%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SLOAD)
                  |};
                  {| EVMInstruction.input := [ inr 0x010000000000000000; inl 1%nat ];
                      EVMInstruction.output := [ 3%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.LT)
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
                      {| EVMInstruction.input := [ inr 0x01; inl 1%nat ];
                      EVMInstruction.output := [ 15%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADD)
                  |};
                  {| EVMInstruction.input := [ inl 15%nat; inr 0x00 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.SSTORE)
                  |};
                  {| EVMInstruction.input := [ inl 15%nat; inl 1%nat ];
                      EVMInstruction.output := [ 16%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.LT)
                  |};
                  {| EVMInstruction.input := [ inl 16%nat ];
                      EVMInstruction.output := [ 17%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ISZERO)
                  |}]
                |};
                {| EVMBlock.bid := 1%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x4e487b71; inr 0xe0 ];
                      EVMInstruction.output := [ 7%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SHL)
                  |};
                  {| EVMInstruction.input := [ inl 7%nat; inr 0x00 ];
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
                |};
                {| EVMBlock.bid := 5%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ReturnBlock [];
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x00; inr 0x00 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |};
                  {| EVMInstruction.input := [ inr 0x20; inr 0x00 ];
                      EVMInstruction.output := [ 23%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.KECCAK256)
                  |};
                  {| EVMInstruction.input := [ inl 1%nat; inl 23%nat ];
                      EVMInstruction.output := [ 24%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADD)
                  |};
                  {| EVMInstruction.input := [ inr 0x00; inl 24%nat ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.SSTORE)
                  |}]
                |};
                {| EVMBlock.bid := 4%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x4e487b71; inr 0xe0 ];
                      EVMInstruction.output := [ 18%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SHL)
                  |};
                  {| EVMInstruction.input := [ inl 18%nat; inr 0x00 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |};
                  {| EVMInstruction.input := [ inr 0x32; inr 0x04 ];
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
      {| EVMFunction.name := "array_copy_storage_to_memory_sol__C__C_44__C_44_deployed__entry";
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
                  {| EVMInstruction.input := [ inl 9%nat; inr 0x26121ff0 ];
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
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 12%nat 6%nat 5%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [ 12%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.CALLVALUE)
                  |}]
                |};
                {| EVMBlock.bid := 6%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 17%nat 9%nat 8%nat;
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
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 21%nat 12%nat 11%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x00 ];
                      EVMInstruction.output := [ 18%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SLOAD)
                  |};
                  {| EVMInstruction.input := [ inr 0x010000000000000000; inl 18%nat ];
                      EVMInstruction.output := [ 20%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.LT)
                  |};
                  {| EVMInstruction.input := [ inl 20%nat ];
                      EVMInstruction.output := [ 21%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ISZERO)
                  |}]
                |};
                {| EVMBlock.bid := 8%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x00; inr 0x00 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.REVERT)
                  |}]
                |};
                {| EVMBlock.bid := 12%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 32%nat 15%nat 14%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x01; inl 18%nat ];
                      EVMInstruction.output := [ 30%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADD)
                  |};
                  {| EVMInstruction.input := [ inl 30%nat; inr 0x00 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.SSTORE)
                  |};
                  {| EVMInstruction.input := [ inl 30%nat; inl 18%nat ];
                      EVMInstruction.output := [ 31%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.LT)
                  |};
                  {| EVMInstruction.input := [ inl 31%nat ];
                      EVMInstruction.output := [ 32%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ISZERO)
                  |}]
                |};
                {| EVMBlock.bid := 11%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x4e487b71; inr 0xe0 ];
                      EVMInstruction.output := [ 23%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SHL)
                  |};
                  {| EVMInstruction.input := [ inl 23%nat; inr 0x00 ];
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
                |};
                {| EVMBlock.bid := 15%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Jump 17%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x00; inr 0x00 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |};
                  {| EVMInstruction.input := [ inr 0x20; inr 0x00 ];
                      EVMInstruction.output := [ 38%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.KECCAK256)
                  |};
                  {| EVMInstruction.input := [ inl 18%nat; inl 38%nat ];
                      EVMInstruction.output := [ 39%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADD)
                  |};
                  {| EVMInstruction.input := [ inr 0x01; inl 39%nat ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.SSTORE)
                  |};
                  {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inl "array_copy_storage_to_memory_sol__C__C_44__C_44_deployed__array_push_from_uint256_to_array_uint256_dyn_storage_ptr")
                  |};
                  {| EVMInstruction.input := [  ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inl "array_copy_storage_to_memory_sol__C__C_44__C_44_deployed__array_push_from_uint256_to_array_uint256_dyn_storage_ptr")
                  |};
                  {| EVMInstruction.input := [ inr 0x40 ];
                      EVMInstruction.output := [ 40%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.MLOAD)
                  |};
                  {| EVMInstruction.input := [ inr 0x00 ];
                      EVMInstruction.output := [ 41%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SLOAD)
                  |};
                  {| EVMInstruction.input := [ inl 41%nat; inl 40%nat ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |};
                  {| EVMInstruction.input := [ inr 0x20; inl 40%nat ];
                      EVMInstruction.output := [ 42%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADD)
                  |};
                  {| EVMInstruction.input := [ inr 0x00; inr 0x00 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |};
                  {| EVMInstruction.input := [ inr 0x290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563 ];
                      EVMInstruction.output := [ 44%nat ];
                      EVMInstruction.op := inr EVMInstruction.ASSIGN
                  |};
                  {| EVMInstruction.input := [ inr 0x00 ];
                      EVMInstruction.output := [ 45%nat ];
                      EVMInstruction.op := inr EVMInstruction.ASSIGN
                  |}]
                |};
                {| EVMBlock.bid := 14%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x4e487b71; inr 0xe0 ];
                      EVMInstruction.output := [ 33%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SHL)
                  |};
                  {| EVMInstruction.input := [ inl 33%nat; inr 0x00 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |};
                  {| EVMInstruction.input := [ inr 0x32; inr 0x04 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |};
                  {| EVMInstruction.input := [ inr 0x24; inr 0x00 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.REVERT)
                  |}]
                |};
                {| EVMBlock.bid := 17%nat;
                   EVMBlock.phi_function := fun blockid => if BlockID.eqb blockid 15%nat then [(47%nat, inl 45%nat); (49%nat, inl 44%nat); (51%nat, inl 42%nat)] else if BlockID.eqb blockid 19%nat then [(47%nat, inl 54%nat); (49%nat, inl 53%nat); (51%nat, inl 52%nat)] else [];
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 48%nat 20%nat 18%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inl 41%nat; inl 47%nat ];
                      EVMInstruction.output := [ 48%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.LT)
                  |}]
                |};
                {| EVMBlock.bid := 20%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 65%nat 22%nat 21%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x1f ];
                      EVMInstruction.output := [ 56%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.NOT)
                  |};
                  {| EVMInstruction.input := [ inl 40%nat; inl 51%nat ];
                      EVMInstruction.output := [ 58%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SUB)
                  |};
                  {| EVMInstruction.input := [ inr 0x1f; inl 58%nat ];
                      EVMInstruction.output := [ 59%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADD)
                  |};
                  {| EVMInstruction.input := [ inl 56%nat; inl 59%nat ];
                      EVMInstruction.output := [ 60%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.AND)
                  |};
                  {| EVMInstruction.input := [ inl 60%nat; inl 40%nat ];
                      EVMInstruction.output := [ 61%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADD)
                  |};
                  {| EVMInstruction.input := [ inl 40%nat; inl 61%nat ];
                      EVMInstruction.output := [ 62%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.LT)
                  |};
                  {| EVMInstruction.input := [ inr 0xffffffffffffffff; inl 61%nat ];
                      EVMInstruction.output := [ 64%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.GT)
                  |};
                  {| EVMInstruction.input := [ inl 62%nat; inl 64%nat ];
                      EVMInstruction.output := [ 65%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.OR)
                  |}]
                |};
                {| EVMBlock.bid := 18%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Jump 19%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inl 49%nat ];
                      EVMInstruction.output := [ 50%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SLOAD)
                  |};
                  {| EVMInstruction.input := [ inl 50%nat; inl 51%nat ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |};
                  {| EVMInstruction.input := [ inr 0x20; inl 51%nat ];
                      EVMInstruction.output := [ 52%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADD)
                  |};
                  {| EVMInstruction.input := [ inr 0x01; inl 49%nat ];
                      EVMInstruction.output := [ 53%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADD)
                  |}]
                |};
                {| EVMBlock.bid := 22%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.ConditionalJump 72%nat 25%nat 24%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inl 61%nat; inr 0x40 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |};
                  {| EVMInstruction.input := [ inl 40%nat ];
                      EVMInstruction.output := [ 71%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.MLOAD)
                  |};
                  {| EVMInstruction.input := [ inl 71%nat ];
                      EVMInstruction.output := [ 72%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ISZERO)
                  |}]
                |};
                {| EVMBlock.bid := 21%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x4e487b71; inr 0xe0 ];
                      EVMInstruction.output := [ 66%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SHL)
                  |};
                  {| EVMInstruction.input := [ inl 66%nat; inr 0x00 ];
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
                |};
                {| EVMBlock.bid := 19%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Jump 17%nat;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x01; inl 47%nat ];
                      EVMInstruction.output := [ 54%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADD)
                  |}]
                |};
                {| EVMBlock.bid := 25%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inl 42%nat ];
                      EVMInstruction.output := [ 79%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.MLOAD)
                  |};
                  {| EVMInstruction.input := [ inl 40%nat ];
                      EVMInstruction.output := [ 82%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.MLOAD)
                  |};
                  {| EVMInstruction.input := [ inl 79%nat; inl 61%nat ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |};
                  {| EVMInstruction.input := [ inr 0x20; inl 61%nat ];
                      EVMInstruction.output := [ 85%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.ADD)
                  |};
                  {| EVMInstruction.input := [ inl 82%nat; inl 85%nat ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |};
                  {| EVMInstruction.input := [ inr 0x40; inl 61%nat ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.RETURN)
                  |}]
                |};
                {| EVMBlock.bid := 24%nat;
                   EVMBlock.phi_function := EVMBlock.PhiInfoD.empty;
                   EVMBlock.exit_info := EVMBlock.ExitInfoD.Terminated;
                   EVMBlock.instructions := [ 
                      {| EVMInstruction.input := [ inr 0x4e487b71; inr 0xe0 ];
                      EVMInstruction.output := [ 73%nat ];
                      EVMInstruction.op := inl (inr EVM_opcode.SHL)
                  |};
                  {| EVMInstruction.input := [ inl 73%nat; inr 0x00 ];
                      EVMInstruction.output := [  ];
                      EVMInstruction.op := inl (inr EVM_opcode.MSTORE)
                  |};
                  {| EVMInstruction.input := [ inr 0x32; inr 0x04 ];
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
      {| EVMFunction.name := "array_copy_storage_to_memory_sol__C__C_44__entry";
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
           EVMSmartContract.main := "array_copy_storage_to_memory_sol__C__C_44__C_44_deployed__array_push_from_uint256_to_array_uint256_dyn_storage_ptr" 
       |}.

Definition liveness_info : FunctionName.t -> option EVMLiveness.fun_live_info_t :=
fun fname =>
   match fname with 
   | "array_copy_storage_to_memory_sol__C__C_44__C_44_deployed__array_push_from_uint256_to_array_uint256_dyn_storage_ptr" => Some (
      fun blockid =>
         match blockid with 
         | 0%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [ 1%nat ])         
         | 2%nat => Some (EVMLiveness.list_to_set [ 1%nat ], EVMLiveness.list_to_set [ 1%nat ])         
         | 1%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 5%nat => Some (EVMLiveness.list_to_set [ 1%nat ], EVMLiveness.list_to_set [  ])         
         | 4%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])
         | _ => None
         end )
   | "array_copy_storage_to_memory_sol__C__C_44__C_44_deployed__entry" => Some (
      fun blockid =>
         match blockid with 
         | 0%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 2%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 1%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 4%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 3%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 6%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 5%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 9%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [ 18%nat ])         
         | 8%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 12%nat => Some (EVMLiveness.list_to_set [ 18%nat ], EVMLiveness.list_to_set [ 18%nat ])         
         | 11%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 15%nat => Some (EVMLiveness.list_to_set [ 18%nat ], EVMLiveness.list_to_set [ 45%nat; 44%nat; 42%nat; 40%nat; 41%nat ])         
         | 14%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 17%nat => Some (EVMLiveness.list_to_set [ 47%nat; 49%nat; 51%nat; 40%nat; 42%nat; 41%nat ], EVMLiveness.list_to_set [ 47%nat; 49%nat; 51%nat; 40%nat; 42%nat; 41%nat ])         
         | 20%nat => Some (EVMLiveness.list_to_set [ 40%nat; 42%nat; 51%nat ], EVMLiveness.list_to_set [ 61%nat; 40%nat; 42%nat ])         
         | 18%nat => Some (EVMLiveness.list_to_set [ 47%nat; 49%nat; 51%nat; 40%nat; 42%nat; 41%nat ], EVMLiveness.list_to_set [ 53%nat; 52%nat; 47%nat; 40%nat; 42%nat; 41%nat ])         
         | 22%nat => Some (EVMLiveness.list_to_set [ 61%nat; 40%nat; 42%nat ], EVMLiveness.list_to_set [ 61%nat; 40%nat; 42%nat ])         
         | 21%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])         
         | 19%nat => Some (EVMLiveness.list_to_set [ 53%nat; 52%nat; 47%nat; 40%nat; 42%nat; 41%nat ], EVMLiveness.list_to_set [ 54%nat; 53%nat; 52%nat; 40%nat; 42%nat; 41%nat ])         
         | 25%nat => Some (EVMLiveness.list_to_set [ 61%nat; 40%nat; 42%nat ], EVMLiveness.list_to_set [  ])         
         | 24%nat => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])
         | _ => None
         end )
   | "array_copy_storage_to_memory_sol__C__C_44__entry" => Some (
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
(* Compute (EVMLiveness.check_smart_contract sc_tr liveness_info). *)
Compute (EVMLiveness.check_smart_contract_subset sc_tr liveness_info).

End Translation.
        