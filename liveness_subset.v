Require Import FORYU.state.
Require Import FORYU.program.
Require Import FORYU.semantics.
Require Import Orders.
Require Import OrdersEx.
Require Import MSets.
Require Import Arith.
Require Import List.
Import ListNotations.
Require Import Coq.Relations.Relation_Operators.
Require Import stdpp.prelude.
Require Import stdpp.relations. (* This is where nsteps lives *)
From Coq Require Import Strings.Ascii.

Require Import Coq.MSets.MSetAVL.
Require Import Coq.Structures.OrdersEx.      (* Provides New Keys *)

Module Liveness_Subset (D: DIALECT).

  Module SmallStepD := SmallStep(D).
  Module StateD := SmallStepD.StateD.
  Module CallStackD := StateD.CallStackD.
  Module StackFrameD := CallStackD.StackFrameD.
  Module LocalsD := StackFrameD.LocalsD.
  Module CFGProgD := CFGProg(D).
  Module CFGFunD := CFGProgD.CFGFunD.
  Module BlockD := CFGProgD.BlockD.
  Module PhiInfoD := BlockD.PhiInfoD.
  Module InstrD := BlockD.InstrD.
  Module ExitInfoD := BlockD.ExitInfoD.
  Module SimpleExprD := ExitInfoD.SimpleExprD.
  
  Import SmallStepD.
  Import StateD.
  Import CallStackD.
  Import StackFrameD.
  Import LocalsD.
  Import CFGProgD.
  Import CFGFunD.
  Import BlockD.
  Import PhiInfoD.
  Import InstrD.
  Import ExitInfoD.
  Import SimpleExprD.
  
  (* This module defines a set of variables. *)
  Module VarSet := MSetAVL.Make(VarID.VarID_as_OT).
  
  (* convert a list to a set *)
  Fixpoint list_to_set (l : list VarID.t) : VarSet.t :=
    match l with
    | nil => VarSet.empty
    | x::xs => VarSet.add x (list_to_set xs)
    end.
  
  (* extracts a list of variables from a list of simple expressions (a
     simple expression is either a variable or of type D.t *)
  Fixpoint extract_yul_vars (l : list SimpleExprD.t) : list VarID.t :=
    match l with
    | nil => nil
    | x::xs =>
        let xs_vs := extract_yul_vars xs in
        match x with
        | inl idx => idx::xs_vs
        | inr _ => xs_vs
        end
    end.
  
  (* Applies the inverse of the phi function. It is like applying the assignment backwards. *)
  Definition apply_inv_phi (renamings: InBlockPhiInfo) (s: VarSet.t) :=
    match renamings with
    | in_phi_info out_vars in_sexprs _ _ => 
        let in_set := list_to_set (extract_yul_vars in_sexprs) in
        let out_set := list_to_set out_vars in
        (VarSet.union (VarSet.diff s out_set) in_set)
    end.
  
  
  (* Propages liveness information one step backwards for an instruction *)
  Definition prop_live_set_bkw_instr (i: InstrD.t) (s: VarSet.t) : VarSet.t :=
    let in_set := list_to_set (extract_yul_vars i.(input)) in
      let out_set := list_to_set i.(output) in
      (VarSet.union (VarSet.diff s out_set) in_set).
  

  
  (* Propagates the liveness information through the first in
  instructions in [l_rev]. Note that [l_rev] is supposed to be the
  reverse of an actual list of instructions -- since the propagation
  starts from the end*)
  Fixpoint prop_live_set_bkw_aux (n: nat) (l_rev: list InstrD.t) (s: VarSet.t) : VarSet.t :=
    match n with
    | 0%nat => s
    | S n' =>
        match l_rev with
        | nil => s
        | i::l_rev' =>
            prop_live_set_bkw_aux n' l_rev' (prop_live_set_bkw_instr i s)
        end
    end.

  
  (* Propagates the liveness information through the list of
  instructions in [l], starting from the end. *)
  Definition prop_live_set_bkw (l: list InstrD.t) (s: VarSet.t) : VarSet.t :=    
    prop_live_set_bkw_aux  (length l) (rev l) s.

  (* Given a block [b], it adds the conditional variable of the block
  is a conditional jump *)
  Definition add_jump_var_if_applicable (b: BlockD.t) (s: VarSet.t) :=
    match b.(BlockD.exit_info) with
    | ExitInfoD.ConditionalJump cond_var _ _ => VarSet.add cond_var s
    | _ => s
      end.

  (* The following types are used to define the result of a live-variable analysis *)
  Definition block_live_info_t := nat -> option VarSet.t.
  Definition func_live_info_t := BlockID.t -> option (VarSet.t * VarSet.t).
  Definition prog_live_info_t := FuncName.t -> option func_live_info_t.


  (*
    Liveness analysis is typically based on solving the following equations:


      liveout(b) = 1. if b is a terminal block, then retvars(b)  
                   2.  if b has successor b1...bn, the \cup inv-phi_{bi}(b,\livein(bi))

      livein(b) =  propbkw(instrs(b), liveout(b) cup condvars(b))

      propbkw(l,s) = if l=i::l then propbkw(l',(s \ writeset(i)) \cup readset(i)) else s

   So we bascally check that the given result f a liveness analysis from a
   solutiopn for these equations.

   Later we also prove that such a solution implies some semantical property,
   givining semantical menaing to liveness.

  *)
  
  (* Checks that the live-in set of a block [b] is sound, meaning that
  it is equivalent to propagating back its live-out set *)
  Definition check_live_in (r: prog_live_info_t) (f: FuncName.t) (b: BlockD.t) : bool :=
    match (r f) with
    | None => false
    | Some f_info =>
      match f_info b.(BlockD.bid) with
      | None => false
      | Some (b_in_info,b_out_info) =>
          (* VarSet.equal b_in_info (prop_live_set_bkw b.(BlockD.instructions) (add_jump_var_if_applicable b b_out_info)) *)
          VarSet.subset b_in_info (prop_live_set_bkw b.(BlockD.instructions) (add_jump_var_if_applicable b b_out_info))
      end
    end.
  
  (* Checks that the live-out set of a block [b] is sound. It handle
  several cases depending on the kid of block *)
  Definition check_live_out (p: CFGProgD.t) (r: prog_live_info_t) (f: FuncName.t) (b: BlockD.t) : bool :=
    match (r f) with
    | None => false
    | Some f_info =>
        match (f_info b.(bid)) with
        | None => false
        | Some (b_in_info,b_out_info) =>
            match b.(exit_info) with
              (* Terminate block has an empty live-out set *)
            | ExitInfoD.Terminate =>
                (* VarSet.equal b_out_info VarSet.empty *)               
                VarSet.subset b_out_info VarSet.empty
                             
              (* The live-out set of a return block is the set of
              variables in its returned expressions *)
            | ExitInfoD.ReturnBlock ret_sexprs => 
                (* VarSet.equal b_out_info (list_to_set (extract_yul_vars ret_sexprs)) *)
                VarSet.subset b_out_info (list_to_set (extract_yul_vars ret_sexprs))

            (* The live-out set of a jump blocks is obtained from the
            live-in of the next block, after applying the inverse of
            the phi-function *)
            | ExitInfoD.Jump next_bid =>
                match (CFGProgD.get_block p f next_bid) with
                | None => false
                | Some next_b =>
                    match (f_info next_bid) with
                    | None => false
                    | Some (next_b_in_info,next_b_out_info) =>
                        (* VarSet.equal b_out_info (apply_inv_phi (BlockD.phi_function next_b b.(BlockD.bid)) next_b_in_info) *)
                        VarSet.subset b_out_info (apply_inv_phi (BlockD.phi_function next_b b.(BlockD.bid)) next_b_in_info)
                    end
                end
                  
            (* Like the case of jump, but takes union for all successors *)
            | ExitInfoD.ConditionalJump cond_var next_bid_if_true next_bid_if_false =>
                match (CFGProgD.get_block p f next_bid_if_true) with
                | None => false
                | Some next_b_if_true =>
                    match (CFGProgD.get_block p f next_bid_if_false) with
                    | None => false
                    | Some next_b_if_false =>
                        match (f_info next_bid_if_true) with
                        | None => false
                        | Some (next_b_ift_in_info,next_b_ift_out_info) =>
                            match (f_info next_bid_if_false) with
                            | None => false
                            | Some (next_b_iff_in_info,next_b_iff_out_info) =>
                               (* VarSet.equal b_out_info (VarSet.union
                                                           (apply_inv_phi (BlockD.phi_function next_b_if_true b.(BlockD.bid)) next_b_ift_in_info)
                                                           (apply_inv_phi (BlockD.phi_function next_b_if_false b.(BlockD.bid)) next_b_iff_in_info)) *)
                                VarSet.subset b_out_info (VarSet.union
                                                           (apply_inv_phi (BlockD.phi_function next_b_if_true b.(BlockD.bid)) next_b_ift_in_info)
                                                           (apply_inv_phi (BlockD.phi_function next_b_if_false b.(BlockD.bid)) next_b_iff_in_info))
                            end
                        end
                    end
                end
            end
        end
    end.

  (* Checks that the liveness information of [b] is sound, i.e., that
  both live-in and live-out are sound *)
  Definition check_live (p: CFGProgD.t) (r: prog_live_info_t) (f: FuncName.t) (b: BlockD.t) : bool :=
    if (check_live_in r f b) then check_live_out p r f b else false.


  (* Checks that liveness information of all blocks in [bs] *)
  Fixpoint check_blocks (bs: list BlockD.t) (fname: FuncName.t) (p: CFGProgD.t) (r: prog_live_info_t) :=
    match bs with
    | nil => true
    | b::bs' => if (check_live p r fname b)
                then check_blocks bs' fname p r
                else false
    end.


  (* Checks  liveness information of all blocks of functions [fs] *)
  Fixpoint check_functions (fs: list CFGFunD.t) (p: CFGProgD.t) (r: prog_live_info_t) :=
    match fs with
    | nil => true
    | f::fs' => if (check_blocks f.(blocks) f.(name) p r)
                then check_functions fs' p r
                else false
    end.

  (* Checks that liveness information of all blocks of all functions [fs] of the program [p] *)
  Definition check_program (p: CFGProgD.t) (r: prog_live_info_t) :=
    check_functions p.(functions) p r.



End Liveness_Subset.
