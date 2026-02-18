Require Export FORYU.program.
Require Export FORYU.semantics.
Require Export FORYU.liveness.
Require Export FORYU.evm_dialect.
Require Import NArith.
Require Import Coq.ZArith.ZArith.
Require Import Arith.
Import ListNotations.

Module Checker.

    Module EVMLiveness := Liveness(EVMDialect).
    Module EVMSmallStep := EVMLiveness.SmallStepD.
    Module EVMCFGProg := EVMSmallStep.CFGProgD.
    Module EVMCFGFun := EVMCFGProg.CFGFunD.
    Module EVMBlock := EVMCFGFun.BlockD.
    Module EVMInstr := EVMBlock.InstrD.
    Module EVMState := EVMSmallStep.StateD.
    Module EVMPhiInfo := EVMBlock.PhiInfoD.
    Module ExitInfo := EVMBlock.ExitInfoD.

    (*Definition myfun (s: ExitInfo.t) := s.*)
    Definition myfun (s: ExitInfo.t) := s.

End Checker.