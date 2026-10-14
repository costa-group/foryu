Require Import FORYU.state.
Require Import FORYU.program.

From Stdlib Require Import MSets.
From Stdlib Require Import List.
From Stdlib Require Import Strings.String.
From Stdlib Require Import MSets.MSetAVL.
From Stdlib Require Import Structures.OrdersEx.

(* Types for representing liveness information. Unlike constancy
   information (constancy_info.v), they do not depend on the dialect,
   since liveness only depends on which variables are read and
   written. *)

(* This module defines a set of variables. *)
Module VarSet := MSetAVL.Make(VarID.VarID_as_OT).

Definition VarSet_show (s: VarSet.t) : string :=
  let vars := VarSet.elements s in
  let var_strings := List.map VarID.show vars in
  "{" ++ String.concat ", " var_strings ++ "}".

(* The liveness information of a function maps each block to its
   live-in and live-out sets *)
Definition func_live_info_t := BlockID.t -> option (VarSet.t * VarSet.t).

(* The liveness information of a program maps each function to its
   liveness information *)
Definition prog_live_info_t := FuncName.t -> option func_live_info_t.
