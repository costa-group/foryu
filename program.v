(*

Data structures for CFG-YUL programs

*)

Require Export FORYU.dialect.
Require Export FORYU.misc.
Require Export Coq.Lists.List.
Import ListNotations.
Require Export Coq.Strings.String.
Require Import MSets.
Require Import NArith.
Require Import Arith.

Require Import Coq.MSets.MSetAVL.
Require Import Coq.Structures.OrdersEx.      (* Provides New Keys *)


Global Open Scope string_scope.
Global Open Scope Z_scope.

 
(* A module for block identifier *)
Module BlockID.
  (* A block ID is a natural number using N ofr effciency. *)
  Definition t := N.

  (* we require boolean equality to reflect equality *)
  Definition eqb := N.eqb.
  Definition eqb_spec := N.eqb_spec.

    (* For rewriting [eqb x y = true] and [x = y] and vice versa *)
  Lemma eqb_eq : forall x y, eqb x y = true <-> x = y.
  Proof.
    intros x y.
    Misc.eqb_eq_from_reflect eqb_spec.    
  Qed.

  (* For rewriting [eqb x y <> true] and [x <> y] *)
  Lemma eqb_neq : forall x y, eqb x y <> true <-> x <> y.
  Proof.
    intros x y.
    Misc.eqb_neq_from_reflect (eqb_spec x y).
  Qed.

  (* For rewriting [eqb x y = false] and [x <> y] *)
  Lemma eqb_neq_false : forall x y, eqb x y = false <-> x <> y.
  Proof.
    intros x y.
    Misc.eqb_neq_from_reflect (eqb_spec x y).
  Qed.
  
  (* [eqb] is reflexive *)
  Lemma eqb_refl : forall x: t, eqb x x = true.
  Proof.
    intro x.
    Misc.eqb_eq_to_eq_refl eqb_eq.
  Qed.

  (* [eq_dec] provides [{x=y}+{x<>y}]. Usually it is not needed as
  [eqb_spec] is enough. *)  
  Definition eq_dec (x y: t): sumbool (x=y) (x<>y).
    Misc.sumbool_from_reflect (eqb_spec x y).
  Defined.

End BlockID.


Module YULVariable.
  (* YUL variables are represented as natural numbers using N for efficiency. *)
  Definition t := N.

  (* we require boolean equality to reflect equality *)
  Definition eqb := N.eqb.
  Definition eqb_spec := N.eqb_spec.

  (* For rewriting [eqb x y = true] and [x = y] and vice versa *)
  Lemma eqb_eq : forall x y, eqb x y = true <-> x = y.
  Proof.
    intros x y.
    Misc.eqb_eq_from_reflect eqb_spec.    
  Qed.

  (* For rewriting [eqb x y <> true] and [x <> y] *)
  Lemma eqb_neq : forall x y, eqb x y <> true <-> x <> y.
  Proof.
    intros x y.
    Misc.eqb_neq_from_reflect (eqb_spec x y).
  Qed.

  (* For rewriting [eqb x y = false] and [x <> y] *)
  Lemma eqb_neq_false : forall x y, eqb x y = false <-> x <> y.
  Proof.
    intros x y.
    Misc.eqb_neq_from_reflect (eqb_spec x y).
  Qed.
  
  (* [eqb] is reflexive *)
  Lemma eqb_refl : forall x: t, eqb x x = true.
  Proof.
    intro x.
    Misc.eqb_eq_to_eq_refl eqb_eq.
  Qed.

  (* [eq_dec] provides [{x=y}+{x<>y}]. Usually it is not needed as
  [eqb_spec] is enough. *)  
  Definition eq_dec (x y: t): sumbool (x=y) (x<>y).
    Misc.sumbool_from_reflect (eqb_spec x y).
  Defined.

 (* It is a UsualOrderedType, we simply use that of N *)
  Module YULVariable_as_OT := OrdersEx.N_as_OT.
End YULVariable.

(* This module defines a set of variables. It is not used here, the
purpose is to use it in analysis that requires such sets. *)
Module YULVarSet := MSetAVL.Make(YULVariable.YULVariable_as_OT).

(* This module defines simple expressions, which can be a variable or a value *)
Module SimpleExpr (D: DIALECT).
  Definition t : Type := YULVariable.t + D.value_t.

  Definition eqb (x y: t): bool :=
    match x, y with
    | inl v1, inl v2 => YULVariable.eqb v1 v2
    | inr v1, inr v2 => D.eqb v1 v2
    | _,_ => false
    end.

  (* we require boolean equality to reflect equality *)
  Lemma eqb_spec : forall x y : t, reflect (x = y) (eqb x y).
  Proof.
    intros x y.
    unfold eqb.
    destruct x as [xvar | xval]; destruct y as [yvar | yval].
    - destruct (YULVariable.eqb_spec xvar yvar) as [Heq | Hneq].
      + rewrite <- YULVariable.eqb_eq in Heq.
        rewrite Heq.
        apply ReflectT.
        rewrite YULVariable.eqb_eq in Heq.
        rewrite Heq.
        reflexivity.
      + rewrite <- YULVariable.eqb_neq_false in Hneq.
        rewrite Hneq.
        apply ReflectF.
        rewrite YULVariable.eqb_neq_false in Hneq.
        intro H_contra.
        injection H_contra as H_contra.
        contradiction.
    -   apply ReflectF.
        intro H_contra.
        discriminate H_contra.

    - apply ReflectF.
      intro H_contra.
      discriminate H_contra.

    - destruct (D.eqb_spec xval yval) as [Heq | Hneq].
      + apply ReflectT.
        rewrite Heq.
        reflexivity.
      + apply ReflectF.
        intro H_contra.
        injection H_contra as H_contra.
        contradiction.
  Qed.

  (* For rewriting [eqb x y = true] and [x = y] and vice versa *)
  Lemma eqb_eq : forall x y, eqb x y = true <-> x = y.
  Proof.
    intros x y.
    Misc.eqb_eq_from_reflect eqb_spec.    
  Qed.

  (* For rewriting [eqb x y <> true] and [x <> y] *)
  Lemma eqb_neq : forall x y, eqb x y <> true <-> x <> y.
  Proof.
    intros x y.
    Misc.eqb_neq_from_reflect (eqb_spec x y).
  Qed.

  (* For rewriting [eqb x y = false] and [x <> y] *)
  Lemma eqb_neq_false : forall x y, eqb x y = false <-> x <> y.
  Proof.
    intros x y.
    Misc.eqb_neq_from_reflect (eqb_spec x y).
  Qed.
  
  (* [eqb] is reflexive *)
  Lemma eqb_refl : forall x: t, eqb x x = true.
  Proof.
    intro x.
    Misc.eqb_eq_to_eq_refl eqb_eq.
  Qed.

  (* [eq_dec] provides [{x=y}+{x<>y}]. Usually it is not needed as
  [eqb_spec] is enough. *)  
  Definition eq_dec (x y: t): sumbool (x=y) (x<>y).
    Misc.sumbool_from_reflect (eqb_spec x y).
  Defined.

End SimpleExpr.

Module FunctionName.
  (* YUL Function names represented as strings. *)
  Definition t := string.

  (* we require boolean equality to reflect equality *)
  Definition eqb := String.eqb.
  Definition eqb_spec := String.eqb_spec.

    (* For rewriting [eqb x y = true] and [x = y] and vice versa *)
  Lemma eqb_eq : forall x y, eqb x y = true <-> x = y.
  Proof.
    intros x y.
    Misc.eqb_eq_from_reflect eqb_spec.    
  Qed.

  (* For rewriting [eqb x y <> true] and [x <> y] *)
  Lemma eqb_neq : forall x y, eqb x y <> true <-> x <> y.
  Proof.
    intros x y.
    Misc.eqb_neq_from_reflect (eqb_spec x y).
  Qed.

  (* For rewriting [eqb x y = false] and [x <> y] *)
  Lemma eqb_neq_false : forall x y, eqb x y = false <-> x <> y.
  Proof.
    intros x y.
    Misc.eqb_neq_from_reflect (eqb_spec x y).
  Qed.
  
  (* [eqb] is reflexive *)
  Lemma eqb_refl : forall x: t, eqb x x = true.
  Proof.
    intro x.
    Misc.eqb_eq_to_eq_refl eqb_eq.
  Qed.

  (* [eq_dec] provides [{x=y}+{x<>y}]. Usually it is not needed as
  [eqb_spec] is enough. *)  
  Definition eq_dec (x y: t): sumbool (x=y) (x<>y).
    Misc.sumbool_from_reflect (eqb_spec x y).
  Defined.

End FunctionName.




Module ExitInfo (D: DIALECT).
  Module SimpleExprD := SimpleExpr(D).
  
  Inductive t : Type := 
  | ConditionalJump (cond_var : YULVariable.t) (target_if_true : BlockID.t) (target_if_false : BlockID.t)
  | Jump (target : BlockID.t)
  | ReturnBlock (return_values : list SimpleExprD.t)
  | Terminated.

End ExitInfo.

Search (NoDup nil).

Module PhiInfo (D: DIALECT).

  Module SimpleExprD := SimpleExpr(D).

  Inductive InBlockPhiInfo :=
  | in_phi_info (out_vars: list YULVariable.t) (in_vars: list SimpleExprD.t) (H_no_dup: List.NoDup out_vars) (H_same_le: length out_vars = length in_vars).
  
  Definition t := BlockID.t -> InBlockPhiInfo.

  (* an empty map for a block *)
  Definition empty_in_phi_info :=
    in_phi_info [] [] (NoDup_nil YULVariable.t) (eq_refl (length [])).

  (* The empty phi function maps every block ID to the empty map. *)
  Definition empty :=  
      fun bid : BlockID.t => empty_in_phi_info.

  Program Definition construct (out_vars: list YULVariable.t) (in_vars: list SimpleExprD.t) : option InBlockPhiInfo :=
    match Misc.nodupb YULVariable.t YULVariable.eqb out_vars with
    | false => None
    | true => match Nat.eqb (length out_vars) (length in_vars) with
              | false => None
              | true  => Some (in_phi_info out_vars in_vars _ _)
              end
    end.
  Next Obligation.
    apply Is_true_eq_right in Heq_anonymous0.
    apply (Misc.nodupb_spec YULVariable.t YULVariable.eqb YULVariable.eqb_eq YULVariable.eq_dec) in Heq_anonymous0.
    exact Heq_anonymous0.
  Defined.

  Next Obligation.
    symmetry in Heq_anonymous.
    rewrite Nat.eqb_eq in Heq_anonymous.
    exact Heq_anonymous.
  Defined.


End PhiInfo.


Module Instruction (D: DIALECT).
  Module SimpleExprD := SimpleExpr(D).

  Inductive aux_inst_t :=
    | ASSIGN. (* This is to allow a simple assignment of the form [v1...vk] := [exp1...expk] at the level of YUL *)
  
  (* An instruction is a pair of a block ID and a YUL variable. *)
  Record t : Type := {
      input : list SimpleExprD.t; 
      output : list YULVariable.t; (* Output variables *)
      op : (FunctionName.t + D.opcode_t) + aux_inst_t;
      H_nodup : NoDup output;
    }.
  
  Program Definition construct (input : list SimpleExprD.t) (output : list YULVariable.t) (op : (FunctionName.t + D.opcode_t) + aux_inst_t) : option t :=
  match Misc.nodupb YULVariable.t YULVariable.eqb output with
  | true => Some ({| input:= input; output:=output; op:= _ |})
  | false => None
  end.
Next Obligation.
  apply Is_true_eq_right in Heq_anonymous.
  apply (Misc.nodupb_spec YULVariable.t YULVariable.eqb YULVariable.eqb_eq YULVariable.eq_dec) in Heq_anonymous.
  exact Heq_anonymous.
Defined.

End Instruction.

(*
How to access the entries of an Instruction i of type Instruction(D).t? 
- i.(Instruction.input) to access the input
- i.(Instruction.output) to access the output
- i.(Instruction.op) to access the operation
*)

Module Block (D: DIALECT).
  Module InstructionD := Instruction(D). (* Required to access Instruction(D) *)
  Module PhiInfoD := PhiInfo(D).
  Module ExitInfoD := ExitInfo(D).
  
  (* Block of code of CFG-YUL *)
  Record t : Type := {
      bid : BlockID.t;
      phi_function : PhiInfoD.t;
      exit_info : ExitInfoD.t;
      instructions : list (InstructionD.t); (* List of instructions in the block *)
    }.

  Definition construct (bid: BlockID.t) (phi_function : PhiInfoD.t) (exit_info : ExitInfoD.t) (instructions : list (InstructionD.t)) :=
    {|
      bid := bid;
      phi_function := phi_function;
      exit_info := exit_info;
      instructions := instructions;
    |}.
  
  Definition is_return_block (b : t) :=
    match b.(exit_info) with
    | ExitInfoD.ReturnBlock rs => Some rs
    | _ => None
    end.

  Definition is_jump_block (b : t) :=
    match b.(exit_info) with
    | ExitInfoD.Jump bid => Some bid
    | _ => None
    end.

  Definition is_cond_jump_block (b : t) :=
    match b.(exit_info) with
    | ExitInfoD.ConditionalJump v bid1 bid2 => Some (v,bid1,bid2)
    | _ => None
    end.

  Definition is_terminated_block (b : t) :=
    match b.(exit_info) with
    | ExitInfoD.Terminated => true
    | _ => false
    end.

End Block.



Module Function (D: DIALECT).
  Module BlockD := Block(D). (* Required to access Block(D) *)
  
    (* A function is a collection of blocks, an entry block ID, and a name. *)
  Record t : Type := {
      name : FunctionName.t;
      arguments : list YULVariable.t; (* Input parameters *)
      blocks : list BlockD.t; (* List of blocks *)
      entry_block_id : BlockID.t; (* The ID of the entry block. *)
      H_nodup : NoDup arguments
    }.

  Program Definition construct (name : FunctionName.t) (arguments : list YULVariable.t) (blocks : list BlockD.t) (entry_block_id : BlockID.t) :=
    match Misc.nodupb YULVariable.t YULVariable.eqb arguments with
    | false => None
    | true => Some {| name := name; blocks := blocks; entry_block_id := entry_block_id; H_nodup := _ |}
    end.
  Next Obligation.
    apply Is_true_eq_right in Heq_anonymous.
    apply (Misc.nodupb_spec YULVariable.t YULVariable.eqb YULVariable.eqb_eq YULVariable.eq_dec) in Heq_anonymous.
    exact Heq_anonymous.
  Defined.

      
  Definition get_block (f: t) (bid: BlockID.t) : option BlockD.t :=
    match List.find (fun b => BlockID.eqb b.(BlockD.bid) bid) f.(blocks) with
    | Some block => Some block
    | None => None
    end.
  
  Definition valid_function (f: t) :=
    forall b,
      In b (blocks f) <-> get_block f b.(BlockD.bid) = Some b.
   
End Function.


Module SmartContract (D: DIALECT).
  Module FunctionD := Function(D). (* Required to access Function(D) *)
  Module BlockD := FunctionD.BlockD.
  
  (* A smart contract is a collection of functions and a main function. *)
  Record t : Type := {
    name : string; (* Name of the smart contract *)
    functions : list FunctionD.t; (* List of functions in the smart contract *)
    main: FunctionName.t; (* The main function of the smart contract *)
  }.

  Definition construct (name : string) (functions : list FunctionD.t) (main: FunctionName.t) :=
    {| name := name; functions := functions; main := main |}.

  Definition get_function (sc: t) (fname: FunctionName.t) : option FunctionD.t :=
    match List.find (fun f => FunctionName.eqb f.(FunctionD.name) fname) sc.(functions) with
    | Some func => Some func
    | None => None
    end.

  Definition get_block (sc: t) (fname: FunctionName.t) (bid: BlockID.t) : option BlockD.t :=
    match get_function sc fname with
    | Some func => FunctionD.get_block func bid
    | None => None
    end.

  Definition get_instruction (sc: t) (fname: FunctionName.t) (bid: BlockID.t) (index: nat) : option BlockD.InstructionD.t :=
    match get_block sc fname bid with
    | Some block =>
        List.nth_error block.(BlockD.instructions) index 
    | None => None
    end.

  Definition get_first_block_id (sc: t) (fname: FunctionName.t) : option BlockID.t :=
    match get_function sc fname with
    | Some func => Some func.(FunctionD.entry_block_id)
    | None => None
    end.

  Definition all_function_name_are_different  (p: t) :=
      forall f,
        In f (functions p) <-> get_function p f.(FunctionD.name) = Some f.

  Definition all_function_are_valid  (p: t) :=
    forall f,
      In f (functions p) -> FunctionD.valid_function f.

  Definition valid_smart_contract (p: t) :=
    all_function_name_are_different p /\ all_function_are_valid p.

  Lemma valid_p_vs_get_block:
    forall p,
      valid_smart_contract p ->
      forall fname bid b,
        get_block p fname bid = Some b <->
          exists f, In f p.(functions)  /\ In b f.(FunctionD.blocks) /\ FunctionName.eqb f.(FunctionD.name) fname = true /\ BlockID.eqb b.(BlockD.bid) bid = true.
  Proof.
    intros p H_valid_p.
    intros f bid b.
    split.
    - intros H_get_block.
      unfold get_block in H_get_block.
      destruct (get_function p f) as [func|] eqn:E_get_function; try discriminate.
      unfold get_function in E_get_function.
      destruct (find (fun f0 : FunctionD.t => FunctionName.eqb (FunctionD.name f0) f)) as [func'|] eqn:E_find_func'; try discriminate.
      injection E_get_function as H_func'_eq_func.
      subst func'.

      unfold FunctionD.get_block in H_get_block.
      destruct (find (fun b : FunctionD.BlockD.t => BlockID.eqb (FunctionD.BlockD.bid b) bid) (FunctionD.blocks func)) as [b'|] eqn:E_find_b'; try discriminate.
        
      injection H_get_block as H_b'_eq_b.
      subst b'.

      pose proof (find_some (fun f0 : FunctionD.t => FunctionName.eqb (FunctionD.name f0) f) (functions p) E_find_func' ) as [H_in_func_pfs H_func_name_eqb_f].
      
      pose proof (find_some (fun b : FunctionD.BlockD.t => BlockID.eqb (FunctionD.BlockD.bid b) bid) (FunctionD.blocks func) E_find_b') as [H_in_b_funcbs H_b_bid_eqb_bid].

      exists func.
      repeat split.
      + apply H_in_func_pfs.
      + apply H_in_b_funcbs.
      + apply H_func_name_eqb_f.
      + apply H_b_bid_eqb_bid.

    - intros H_exists_f0.
      destruct H_exists_f0 as [f0 [In_f0_pfs [In_b_f0bs [H_f0_name_eqb_f H_b_bid_eqb_b]]]].

      apply FunctionName.eqb_eq in H_f0_name_eqb_f.
      subst f.

      apply BlockID.eqb_eq in H_b_bid_eqb_b.
      subst bid.
      
      
      unfold valid_smart_contract in H_valid_p.
      destruct H_valid_p as [H_all_fname_diff H_all_f_valid].

      
      unfold all_function_name_are_different in H_all_fname_diff.
      unfold all_function_are_valid in H_all_f_valid.

      unfold get_block.

      pose proof (H_all_fname_diff f0) as H_get_function_f0.
      pose proof (H_all_f_valid f0 In_f0_pfs) as H_f0_valid.
      unfold FunctionD.valid_function in H_f0_valid.

      rewrite H_get_function_f0 in In_f0_pfs.
      rewrite In_f0_pfs.
      
      rewrite H_f0_valid in In_b_f0bs.
      apply In_b_f0bs.
  Qed.

End SmartContract.
