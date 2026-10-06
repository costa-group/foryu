Require Export FORYU.program.
Require Export FORYU.semantics.
Require Export FORYU.evm_dialect.
Require Export FORYU.liveness.
(*Require Export FORYU.liveness_subset.*)
Require Export FORYU.constancy.
Require Export FORYU.evm_constancy.

From Stdlib Require Import NArith.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Arith.
Import ListNotations.

(* Module to load all the relevant datatypes and export them into
OCaml. It is parameterized by the implementation [BC] of the blockchain
operations of the EVM dialect (see evm_dialect.v). *)
Module CheckerF (BC: BLOCK_CHAIN).

    Module EVMDialectBC := EVMDialect(BC).
    Module EVMConstSymbBC := EVMConstSymb(BC).

    Module EVMLiveness := Liveness(EVMDialectBC).
    Module EVMSmallStep := EVMLiveness.SmallStepD.
    Module EVMCFGProg := EVMSmallStep.CFGProgD.
    Module EVMCFGFun := EVMCFGProg.CFGFunD.
    Module EVMBlock := EVMCFGFun.BlockD.
    Module EVMInstr := EVMBlock.InstrD.
    Module EVMState := EVMSmallStep.StateD.
    Module EVMPhiInfo := EVMBlock.PhiInfoD.
    Module ExitInfo := EVMBlock.ExitInfoD.
    Module EVMConstancy := Constancy(EVMDialectBC)(EVMConstSymbBC).

End CheckerF.

(* The checker that is extracted to OCaml, with the default
implementation of the blockchain operations *)
Module Checker := CheckerF(DefaultBlockChain).