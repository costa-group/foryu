Require Export FORYU.program.
Require Export FORYU.semantics.
Require Export FORYU.evm_dialect.
Require Export FORYU.liveness.
(*Require Export FORYU.liveness_subset.*)

From Stdlib Require Import NArith.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Arith.
Import ListNotations.

Module Checker.
    (* Module to load all the relevant datatypes and export them into OCaml *)

    Module EVMLiveness := Liveness(EVMDialect).
    Module EVMSmallStep := EVMLiveness.SmallStepD.
    Module EVMCFGProg := EVMSmallStep.CFGProgD.
    Module EVMCFGFun := EVMCFGProg.CFGFunD.
    Module EVMBlock := EVMCFGFun.BlockD.
    Module EVMInstr := EVMBlock.InstrD.
    Module EVMState := EVMSmallStep.StateD.
    Module EVMPhiInfo := EVMBlock.PhiInfoD.
    Module ExitInfo := EVMBlock.ExitInfoD.
        
End Checker.