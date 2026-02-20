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


Module VarID.
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
  Module VarID_as_OT := OrdersEx.N_as_OT.
End VarID.


(* This module defines simple expressions, which can be a variable or a value *)
Module SimpleExpr (D: DIALECT).
  Definition t : Type := VarID.t + D.value_t.

  Definition eqb (x y: t): bool :=
    match x, y with
    | inl v1, inl v2 => VarID.eqb v1 v2
    | inr v1, inr v2 => D.eqb v1 v2
    | _,_ => false
    end.

  (* we require boolean equality to reflect equality *)
  Lemma eqb_spec : forall x y : t, reflect (x = y) (eqb x y).
  Proof.
    intros x y.
    unfold eqb.
    destruct x as [xvar | xval]; destruct y as [yvar | yval].
    - destruct (VarID.eqb_spec xvar yvar) as [Heq | Hneq].
      + rewrite <- VarID.eqb_eq in Heq.
        rewrite Heq.
        apply ReflectT.
        rewrite VarID.eqb_eq in Heq.
        rewrite Heq.
        reflexivity.
      + rewrite <- VarID.eqb_neq_false in Hneq.
        rewrite Hneq.
        apply ReflectF.
        rewrite VarID.eqb_neq_false in Hneq.
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

Module FuncName.
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

End FuncName.




Module ExitInfo (D: DIALECT).
  Module SimpleExprD := SimpleExpr(D).
  
  Inductive t : Type := 
  | ConditionalJump (cond_var_id : VarID.t) (bid_if_true : BlockID.t) (bid_if_false : BlockID.t)
  | Jump (bid : BlockID.t)
  | ReturnBlock (ret_eexprs : list SimpleExprD.t)
  | Terminate.

End ExitInfo.


Module PhiInfo (D: DIALECT).

  Module SimpleExprD := SimpleExpr(D).

  Inductive InBlockPhiInfo :=
  | in_phi_info (out_vars: list VarID.t) (in_sexprs: list SimpleExprD.t) (H_no_dup: List.NoDup out_vars) (H_same_le: length out_vars = length in_sexprs).
  
  Definition t := BlockID.t -> InBlockPhiInfo.

  (* an empty map for a block *)
  Definition empty_in_phi_info :=
    in_phi_info [] [] (NoDup_nil VarID.t) (eq_refl (length [])).

  (* The empty phi function maps every block ID to the empty map. *)
  Definition empty :=  
      fun bid : BlockID.t => empty_in_phi_info.

  (* IMPORTANT: when there is an error, it uses a defualt value
  instead of failing. It is done this way so the current parser keeps
  working, should be changed one the new parser is tready *)
  Program Definition construct (out_vars: list VarID.t) (in_vars: list SimpleExprD.t) :  InBlockPhiInfo :=
    match Misc.nodupb VarID.t VarID.eqb out_vars with
    | false => empty_in_phi_info
    | true => match Nat.eqb (length out_vars) (length in_vars) with
              | false => empty_in_phi_info
              | true  => (in_phi_info out_vars in_vars _ _)
              end
    end.
  Next Obligation.
    apply Is_true_eq_right in Heq_anonymous0.
    apply (Misc.nodupb_spec VarID.t VarID.eqb VarID.eqb_eq VarID.eq_dec) in Heq_anonymous0.
    exact Heq_anonymous0.
  Defined.

  Next Obligation.
    symmetry in Heq_anonymous.
    rewrite Nat.eqb_eq in Heq_anonymous.
    exact Heq_anonymous.
  Defined.

  Definition construct_ (l: list (VarID.t * SimpleExprD.t)) :  InBlockPhiInfo :=
    let vars := List.map (fun p => fst p) l in
    let exps := List.map (fun p => snd p) l in
    construct vars exps.


End PhiInfo.


Module Instr (D: DIALECT).
  Module SimpleExprD := SimpleExpr(D).

  Inductive aux_inst_t :=
    | ASSIGN. (* This is to allow a simple assignment of the form [v1...vk] := [exp1...expk] at the level of YUL *)
  
  (* An instruction is a pair of a block ID and a YUL variable. *)
  Record t : Type := {
      input : list SimpleExprD.t; 
      output : list VarID.t; (* Output variables *)
      op : (FuncName.t + D.opcode_t) + aux_inst_t;
      H_nodup : NoDup output;
    }.
  
  (* IMPORTANT: when there is an error, it uses a defualt value
  instead of failing. It is done this way so the current parser keeps
  working, should be changed one the new parser is tready *)
  Program Definition construct (input : list SimpleExprD.t) (output : list VarID.t) (op : (FuncName.t + D.opcode_t) + aux_inst_t) : t :=
  match Misc.nodupb VarID.t VarID.eqb output with
  | true => {| input:= input; output:=output; op:= _ |}
  | false => {| input:= []; output:=[]; op:=op; H_nodup := (NoDup_nil VarID.t) |}
  end.
Next Obligation.
  apply Is_true_eq_right in Heq_anonymous.
  apply (Misc.nodupb_spec VarID.t VarID.eqb VarID.eqb_eq VarID.eq_dec) in Heq_anonymous.
  exact Heq_anonymous.
Defined.

End Instr.


Module Block (D: DIALECT).
  Module InstrD := Instr(D). (* Required to access Instr(D) *)
  Module PhiInfoD := PhiInfo(D).
  Module ExitInfoD := ExitInfo(D).
  
  (* Block of code of CFG-YUL *)
  Record t : Type := {
      bid : BlockID.t;
      phi_function : PhiInfoD.t;
      exit_info : ExitInfoD.t;
      instructions : list (InstrD.t); (* List of instructions in the block *)
    }.

  Definition construct (bid: BlockID.t) (phi_function : PhiInfoD.t) (exit_info : ExitInfoD.t) (instructions : list (InstrD.t)) :=
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
    | ExitInfoD.Terminate => true
    | _ => false
    end.

End Block.



Module CFGFun (D: DIALECT).
  Module BlockD := Block(D). (* Required to access Block(D) *)
  
    (* A function is a collection of blocks, an entry block ID, and a name. *)
  Record t : Type := {
      name : FuncName.t;
      args : list VarID.t; (* Input parameters *)
      blocks : list BlockD.t; (* List of blocks *)
      entry_bid : BlockID.t; (* The ID of the entry block. *)
      H_nodup : NoDup args
    }.

  Program Definition construct (name : FuncName.t) (args : list VarID.t) (blocks : list BlockD.t) (entry_bid : BlockID.t) : t :=
    match Misc.nodupb VarID.t VarID.eqb args with
    | false => {| name := name; blocks := []; entry_bid := entry_bid; H_nodup := (NoDup_nil VarID.t)|}
    | true => {| name := name; blocks := blocks; entry_bid := entry_bid; H_nodup := _ |}
    end.
  Next Obligation.
    apply Is_true_eq_right in Heq_anonymous.
    apply (Misc.nodupb_spec VarID.t VarID.eqb VarID.eqb_eq VarID.eq_dec) in Heq_anonymous.
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

End CFGFun.


Module CFGProg (D: DIALECT).
  Module CFGFunD := CFGFun(D). (* Required to access Function(D) *)
  Module BlockD := CFGFunD.BlockD.
  Module InstrD := BlockD.InstrD.
  
  (* A smart contract is a collection of functions and a main function. *)
  Record t : Type := {
    name : string; (* Name of the smart contract *)
    functions : list CFGFunD.t; (* List of functions in the smart contract *)
    main: FuncName.t; (* The main function of the smart contract *)
  }.

  Definition construct (name : string) (main: FuncName.t) (functions : list CFGFunD.t) : t :=
    {| name := name; functions := functions; main := main |}.

  Definition get_func (sc: t) (fname: FuncName.t) : option CFGFunD.t :=
    match List.find (fun f => FuncName.eqb f.(CFGFunD.name) fname) sc.(functions) with
    | Some func => Some func
    | None => None
    end.

  Definition get_block (sc: t) (fname: FuncName.t) (bid: BlockID.t) : option BlockD.t :=
    match get_func sc fname with
    | Some func => CFGFunD.get_block func bid
    | None => None
    end.

  Definition get_instr (sc: t) (fname: FuncName.t) (bid: BlockID.t) (index: nat) : option InstrD.t :=
    match get_block sc fname bid with
    | Some block =>
        List.nth_error block.(BlockD.instructions) index 
    | None => None
    end.

  Definition get_entry_bid (sc: t) (fname: FuncName.t) : option BlockID.t :=
    match get_func sc fname with
    | Some func => Some func.(CFGFunD.entry_bid)
    | None => None
    end.

  Definition all_function_name_are_different  (p: t) :=
      forall f,
        In f (functions p) <-> get_func p f.(CFGFunD.name) = Some f.

  Definition all_function_are_valid  (p: t) :=
    forall f,
      In f (functions p) -> CFGFunD.valid_function f.

  Definition valid_program (p: t) :=
    all_function_name_are_different p /\ all_function_are_valid p.

  Lemma valid_p_vs_get_block:
    forall p,
      valid_program p ->
      forall fname bid b,
        get_block p fname bid = Some b <->
          exists f, In f p.(functions)  /\ In b f.(CFGFunD.blocks) /\ FuncName.eqb f.(CFGFunD.name) fname = true /\ BlockID.eqb b.(BlockD.bid) bid = true.
  Proof.
    intros p H_valid_p.
    intros f bid b.
    split.
    - intros H_get_block.
      unfold get_block in H_get_block.
      destruct (get_func p f) as [func|] eqn:E_get_func; try discriminate.
      unfold get_func in E_get_func.
      destruct (find (fun f0 : CFGFunD.t => FuncName.eqb (CFGFunD.name f0) f)) as [func'|] eqn:E_find_func'; try discriminate.
      injection E_get_func as H_func'_eq_func.
      subst func'.

      unfold CFGFunD.get_block in H_get_block.
      destruct (find (fun b : CFGFunD.BlockD.t => BlockID.eqb (CFGFunD.BlockD.bid b) bid) (CFGFunD.blocks func)) as [b'|] eqn:E_find_b'; try discriminate.
        
      injection H_get_block as H_b'_eq_b.
      subst b'.

      pose proof (find_some (fun f0 : CFGFunD.t => FuncName.eqb (CFGFunD.name f0) f) (functions p) E_find_func' ) as [H_in_func_pfs H_func_name_eqb_f].
      
      pose proof (find_some (fun b : CFGFunD.BlockD.t => BlockID.eqb (CFGFunD.BlockD.bid b) bid) (CFGFunD.blocks func) E_find_b') as [H_in_b_funcbs H_b_bid_eqb_bid].

      exists func.
      repeat split.
      + apply H_in_func_pfs.
      + apply H_in_b_funcbs.
      + apply H_func_name_eqb_f.
      + apply H_b_bid_eqb_bid.

    - intros H_exists_f0.
      destruct H_exists_f0 as [f0 [In_f0_pfs [In_b_f0bs [H_f0_name_eqb_f H_b_bid_eqb_b]]]].

      apply FuncName.eqb_eq in H_f0_name_eqb_f.
      subst f.

      apply BlockID.eqb_eq in H_b_bid_eqb_b.
      subst bid.
      
      
      unfold valid_program in H_valid_p.
      destruct H_valid_p as [H_all_fname_diff H_all_f_valid].

      
      unfold all_function_name_are_different in H_all_fname_diff.
      unfold all_function_are_valid in H_all_f_valid.

      unfold get_block.

      pose proof (H_all_fname_diff f0) as H_get_func_f0.
      pose proof (H_all_f_valid f0 In_f0_pfs) as H_f0_valid.
      unfold CFGFunD.valid_function in H_f0_valid.

      rewrite H_get_func_f0 in In_f0_pfs.
      rewrite In_f0_pfs.
      
      rewrite H_f0_valid in In_b_f0bs.
      apply In_b_f0bs.
  Qed.

End CFGProg.
