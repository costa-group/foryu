(* 
FORYU: Automatic translation for liveness analysis
Smart contract: constant_variables.sol 
Date: 2026-02-07 14:40:29.612652

Compile with:
$ coqc -R . FORYU filename.v

*)

Require Export FORYU.program.
Require Export FORYU.semantics.
Require Export FORYU.liveness.
Require Export FORYU.evm_dialect.
Require Import NArith.
Require Import Coq.ZArith.ZArith.
Require Import Arith.
Import ListNotations.

Module EVMLiveness := Liveness(EVMDialect).
Module EVMSmallStep := EVMLiveness.SmallStepD.
Module EVMCFGProg := EVMSmallStep.CFGProgD.
Module EVMCFGFun := EVMCFGProg.CFGFunD.
Module EVMBlock := EVMCFGFun.BlockD.
Module EVMInstr := EVMBlock.InstrD.
Module EVMState := EVMSmallStep.StateD.
Module EVMPhiInfo := EVMBlock.PhiInfoD.

Module TestTranslation.

Definition sc_tr : EVMCFGProg.t := EVMCFGProg.construct "constant_variables.sol" "constant_variables_sol__Foo__Foo_17__Foo_17_deployed__entry" [ (EVMCFGFun.construct "constant_variables_sol__Foo__Foo_17__Foo_17_deployed__entry" [] [ (EVMBlock.construct 0%N (EVMPhiInfo.empty) (EVMBlock.ExitInfoD.Terminate) [ (EVMInstr.construct [ inr (U256.to_t 0x00); inr (U256.to_t 0x00) ] [  ] (inl (inr EVM_opcode.REVERT))) ]) ] 0%N) ;
 (EVMCFGFun.construct "constant_variables_sol__Foo__Foo_17__entry" [] [ (EVMBlock.construct 0%N (EVMPhiInfo.empty) (EVMBlock.ExitInfoD.ConditionalJump 2%N 2%N%N 1%N%N) [ (EVMInstr.construct [  ] [ 0%N ] (inl (inr EVM_opcode.MEMORYGUARD))) ;
 (EVMInstr.construct [ inl 0%N; inr (U256.to_t 0x40) ] [  ] (inl (inr EVM_opcode.MSTORE))) ;
 (EVMInstr.construct [  ] [ 2%N ] (inl (inr EVM_opcode.CALLVALUE))) ]) ; (EVMBlock.construct 2%N (EVMPhiInfo.empty) (EVMBlock.ExitInfoD.Terminate) [ (EVMInstr.construct [  ] [ 4%N ] (inl (inr EVM_opcode.DATASIZE))) ;
 (EVMInstr.construct [  ] [ 5%N ] (inl (inr EVM_opcode.DATAOFFSET))) ;
 (EVMInstr.construct [ inl 4%N; inl 5%N; inl 0%N ] [  ] (inl (inr EVM_opcode.CODECOPY))) ;
 (EVMInstr.construct [ inl 4%N; inl 0%N ] [  ] (inl (inr EVM_opcode.RETURN))) ]) ; (EVMBlock.construct 1%N (EVMPhiInfo.empty) (EVMBlock.ExitInfoD.Terminate) [ (EVMInstr.construct [ inr (U256.to_t 0x00); inr (U256.to_t 0x00) ] [  ] (inl (inr EVM_opcode.REVERT))) ]) ] 0%N) ]. 

Definition liveness_info : FuncName.t -> option EVMLiveness.func_live_info_t :=
fun fname =>
   match fname with 
   | "constant_variables_sol__Foo__Foo_17__Foo_17_deployed__entry" => Some (
      fun blockid =>
         match blockid with 
         | 0%N => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])
         | _ => None
         end )
   | "constant_variables_sol__Foo__Foo_17__entry" => Some (
      fun blockid =>
         match blockid with 
         | 0%N => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [ 0%N ])         
         | 2%N => Some (EVMLiveness.list_to_set [ 0%N ], EVMLiveness.list_to_set [  ])         
         | 1%N => Some (EVMLiveness.list_to_set [  ], EVMLiveness.list_to_set [  ])
         | _ => None
         end )
   | _ => None
   end.

Definition check := EVMLiveness.check_program sc_tr liveness_info.
(* Launches liveness check *)

End TestTranslation.