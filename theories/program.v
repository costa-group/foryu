(*

Data structures for CFG-YUL programs

*)

Require Export FORYU.misc.
Require Export FORYU.dialect.
Require Export FORYU.misc.
From Stdlib Require Export Lists.List.
Import ListNotations.
From Stdlib Require Export Strings.String.
From Stdlib Require Import MSets.
From Stdlib Require Import NArith.
From Stdlib Require Import Arith.
From Stdlib Require Import FSets.FMapAVL.
From Stdlib Require Import FSets.FMapFacts.
From Stdlib Require Import Structures.OrderedTypeEx.

Global Open Scope string_scope.
Global Open Scope Z_scope.




(* A module for block identifier *)
Module BlockID.
  (* A block ID is a natural number using N fir efficiency. *)
  Definition t := N.

  Definition show (bid: t) : string := 
  "Block" ++ Misc.n_to_string bid.

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

  Definition show (vid: t) : string := 
  "v" ++ Misc.n_to_string vid.

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

  Definition show (e: t) : string :=
    match e with
    | inl v => VarID.show v
    | inr val => D.show_value val
    end.

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

  Definition show (fname: t) : string := fname.

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


(* Finite maps used by [CFGFun.get_block]/[CFGProg.get_func] below to
resolve a block/function in O(log n) instead of the O(n) linear scan a
[List.find] over [blocks]/[functions] would cost -- and since these are
looked up once per CFG edge, across every block of a function, an O(n)
lookup makes the whole check O(n^2). [BlockID.t]/[FuncName.t] don't depend
on any dialect, so these maps are defined once, up front, rather than
inside the [CFGFun(D)]/[CFGProg(D)] functors. *)
Module BlockMap := FMapAVL.Make(N_as_OT).
Module BlockMapFacts := FMapFacts.WFacts_fun N_as_OT BlockMap.

Module FuncNameMap := FMapAVL.Make(String_as_OT).
Module FuncNameMapFacts := FMapFacts.WFacts_fun String_as_OT FuncNameMap.




Module ExitInfo (D: DIALECT).
  Module SimpleExprD := SimpleExpr(D).
  
  Inductive t : Type := 
  | ConditionalJump (cond_var_id : VarID.t) (bid_if_true : BlockID.t) (bid_if_false : BlockID.t)
  | Jump (bid : BlockID.t)
  | ReturnBlock (ret_eexprs : list SimpleExprD.t)
  | Terminate.

  Definition show (e: t) : string :=
    match e with
    | ConditionalJump cond_var_id bid_if_true bid_if_false =>
        "ConditionalJump " ++ VarID.show cond_var_id ++ " " ++ BlockID.show bid_if_true ++ " " ++ BlockID.show bid_if_false
    | Jump bid => "Jump " ++ BlockID.show bid
    | ReturnBlock ret_eexprs => "ReturnBlock " ++ String.concat ", " (List.map SimpleExprD.show ret_eexprs)
    | Terminate => "Terminate"
    end.

End ExitInfo.


Module PhiInfo (D: DIALECT).

  Module SimpleExprD := SimpleExpr(D).

  Inductive InBlockPhiInfo :=
  (*| in_phi_info (out_vars: list VarID.t) (in_sexprs: list SimpleExprD.t).*)
  | in_phi_info (in_sexprs: list SimpleExprD.t).
  
  Definition t := BlockID.t -> InBlockPhiInfo.

  (* [bids] are the candidate predecessor block IDs to probe [phi_info]
  with -- in practice, the enclosing function's blocks (see [Block.show]),
  since [phi_info] returns the empty [InBlockPhiInfo] for anything that is
  not an actual predecessor, so scanning a superset of the real
  predecessors is harmless: [show_in_block_phi_info] filters those down to
  "" and they get dropped below. *)
  Definition show (bids: list BlockID.t) (phi_info: t) : string :=
    let show_in_block_phi_info (bid: BlockID.t) (in_phi_info: InBlockPhiInfo) : string :=
        match in_phi_info with
        | in_phi_info in_sexprs =>
            match in_sexprs with
            | [] => ""
            | _ => BlockID.show bid ++ ": " ++ String.concat ", " (List.map SimpleExprD.show in_sexprs)
            end
        end
    in
    let phi_info_strings : list string := List.map (fun bid => show_in_block_phi_info bid (phi_info bid)) bids in
    let phi_info_strings_clean : list string :=
      List.filter (fun s => negb (String.eqb s "")) phi_info_strings in
    match phi_info_strings_clean with
    | [] => ""
    | _ => String.concat "\n        " phi_info_strings_clean
    end.

  (* an empty map for a block *)
  Definition empty_in_phi_info :=
    in_phi_info [].

  (* The empty phi function maps every block ID to the empty map. *)
  Definition empty :=  
      fun bid : BlockID.t => empty_in_phi_info.

  Definition construct (in_vars: list SimpleExprD.t) : InBlockPhiInfo :=
    in_phi_info in_vars.
  
  Definition construct_ (l: list (VarID.t * SimpleExprD.t)) :  InBlockPhiInfo :=
    let exps := List.map (fun p => snd p) l in
    construct exps.

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

  Definition show (i: t) : string :=
    let op_str := match i.(op) with
                  | inl (inl fname) => FuncName.show fname
                  | inl (inr opcode) => D.show_opcode opcode
                  | inr aux_op =>
                    match aux_op with
                    | ASSIGN => ""
                    end
                  end in
    let input_str := "[" ++ (String.concat ", " (List.map SimpleExprD.show i.(input))) ++ "]" in
    let output_str := "[" ++ (String.concat ", " (List.map VarID.show i.(output))) ++ "]" in
    match i.(output) with
    | [] => "        " ++ op_str ++ " " ++ input_str
    | _ => "        " ++ output_str ++ " := " ++ op_str ++ " " ++ input_str
    end.
    
  
  (* IMPORTANT: when there is an error, it uses a default value
  instead of failing. It is done this way so the current parser keeps
  working, should be changed one the new parser is ready *)
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
      phi_function : (list VarID.t) * PhiInfoD.t; (* out_vars & mapping BlockID -> in_exps *)
      exit_info : ExitInfoD.t;
      instructions : list (InstrD.t); (* List of instructions in the block *)
      H_phi_nodup : NoDup (fst phi_function); (* a block's phi-defined
      out-vars must be duplicate-free: [phi_source]'s own first-match
      lookup and the runtime's last-write-wins [set_all] semantics
      only agree when there is at most one occurrence of each variable
      to begin with (mirrors [InstrD.H_nodup] for the exact same
      reason, one level up) *)
    }.

  (* [all_bids] are the enclosing function's block IDs, passed down from
  [CFGFun.show] so [PhiInfoD.show] can scan the actual candidate
  predecessors instead of a hardcoded range. *)
  Definition show (all_bids: list BlockID.t) (b: t) : string :=
    let (out_vars, phi_info) := b.(phi_function) in
    let out_vars_str := "[" ++ (String.concat ", " (List.map VarID.show out_vars)) ++ "]" in
    let phi_str := PhiInfoD.show all_bids phi_info in
    let phi_str_format := match phi_str with
                        | "" => "\n"
                        | _ => "\n        " ++ phi_str ++ "\n"
                        end in
    "\n\n    ##" ++ BlockID.show b.(bid) ++ "##\n" ++
    "    Phi function: " ++ out_vars_str ++ " := " ++phi_str_format ++
    "    Exit info: " ++ ExitInfoD.show b.(exit_info) ++ "\n" ++
    "    Instructions:\n" ++ String.concat "\n" (List.map InstrD.show b.(instructions)).

  (* IMPORTANT: mirrors [InstrD.construct] -- when [out_vars] has
  duplicates, it uses a default (empty out-vars) value instead of
  failing, for the same reason: keeping the current parser working
  until it is updated to guarantee this itself. *)
  Program Definition construct (bid: BlockID.t) (out_vars: list VarID.t) (phi_function : PhiInfoD.t) (exit_info : ExitInfoD.t) (instructions : list (InstrD.t)) : t :=
    match Misc.nodupb VarID.t VarID.eqb out_vars with
    | true => {| bid := bid; phi_function := (out_vars, phi_function); exit_info := exit_info; instructions := instructions; H_phi_nodup := _ |}
    | false => {| bid := bid; phi_function := ([], phi_function); exit_info := exit_info; instructions := instructions; H_phi_nodup := (NoDup_nil VarID.t) |}
    end.
  Next Obligation.
    apply Is_true_eq_right in Heq_anonymous.
    apply (Misc.nodupb_spec VarID.t VarID.eqb VarID.eqb_eq VarID.eq_dec) in Heq_anonymous.
    exact Heq_anonymous.
  Defined.
  
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

  (* [build_block_index]/[get_block] resolve a block by id via [BlockMap]
  (O(log n)) instead of scanning [blocks] (O(n)) on every call -- see the
  comment on [BlockMap] above. *)
  Definition build_block_index (bs: list BlockD.t) : BlockMap.t BlockD.t :=
    List.fold_left (fun acc b => BlockMap.add b.(BlockD.bid) b acc) bs (BlockMap.empty BlockD.t).

    (* A function is a collection of blocks, an entry block ID, and a name. *)
  Record t : Type := {
      name : FuncName.t;
      args : list VarID.t; (* Input parameters *)
      blocks : list BlockD.t; (* List of blocks *)
      entry_bid : BlockID.t; (* The ID of the entry block. *)
      H_nodup : NoDup args;
      block_index : BlockMap.t BlockD.t; (* built once by [construct] from [blocks], via [build_block_index] *)
      (* Prop-sorted (erased by extraction, like [H_nodup]): ties
      [block_index] to [blocks] as an invariant of the type itself, so
      [get_block]'s soundness ([get_block_sound] below) holds
      unconditionally for every [f : t] instead of only for those built
      by [construct] specifically. *)
      H_block_index : block_index = build_block_index blocks
    }.

  Definition show (f: t) : string :=
    let all_bids := List.map (fun b => b.(BlockD.bid)) f.(blocks) in
    "--------------------------------------\n" ++
    "Function " ++ FuncName.show f.(name) ++ "(" ++ String.concat ", " (List.map VarID.show f.(args)) ++ ")\n" ++
    "Entry: " ++ BlockID.show f.(entry_bid) ++ "\n" ++
    "Blocks:\n" ++
    String.concat "\n" (List.map (BlockD.show all_bids) f.(blocks)) ++
    "\n--------------------------------------\n".

  Program Definition construct (name : FuncName.t) (args : list VarID.t) (blocks : list BlockD.t) (entry_bid : BlockID.t) : t :=
    match Misc.nodupb VarID.t VarID.eqb args with
    | false => {| name := name; blocks := []; entry_bid := entry_bid; H_nodup := (NoDup_nil VarID.t);
                  block_index := build_block_index []; H_block_index := eq_refl |}
    | true => {| name := name; blocks := blocks; entry_bid := entry_bid; H_nodup := _;
                  block_index := build_block_index blocks; H_block_index := eq_refl |}
    end.
  Next Obligation.
    apply Is_true_eq_right in Heq_anonymous.
    apply (Misc.nodupb_spec VarID.t VarID.eqb VarID.eqb_eq VarID.eq_dec) in Heq_anonymous.
    exact Heq_anonymous.
  Defined.

  Definition get_block (f: t) (bid: BlockID.t) : option BlockD.t :=
    BlockMap.find bid f.(block_index).

  (* Generalizes [build_block_index_sound] below to an arbitrary starting
  accumulator [acc], so the induction on [bs] can go through: at each step
  the result found either comes from the [x] just folded in (covered by
  [In]) or was already reachable through [acc] (covered by the recursive
  disjunct, discharged by the invariant hypothesis once [bs] is empty). *)
  Lemma build_block_index_aux_sound :
    forall (bs: list BlockD.t) (acc: BlockMap.t BlockD.t) (bid: BlockID.t) (b: BlockD.t),
      (forall b', BlockMap.find bid acc = Some b' -> b'.(BlockD.bid) = bid) ->
      BlockMap.find bid (List.fold_left (fun a x => BlockMap.add x.(BlockD.bid) x a) bs acc) = Some b ->
      b.(BlockD.bid) = bid /\ (In b bs \/ BlockMap.find bid acc = Some b).
  Proof.
    induction bs as [| x xs IH]; intros acc bid b Hinv Hfind.
    - simpl in Hfind. split.
      + apply Hinv. exact Hfind.
      + right. exact Hfind.
    - simpl in Hfind.
      assert (Hinv' : forall b', BlockMap.find bid (BlockMap.add x.(BlockD.bid) x acc) = Some b' -> b'.(BlockD.bid) = bid).
      { intros b' Hb'.
        rewrite BlockMapFacts.add_o in Hb'.
        destruct (BlockMapFacts.eq_dec x.(BlockD.bid) bid) as [Heq | Hneq].
        - injection Hb' as Hb'. subst b'. exact Heq.
        - apply Hinv. exact Hb'.
      }
      destruct (IH (BlockMap.add x.(BlockD.bid) x acc) bid b Hinv' Hfind) as [Hbid [Hin | Hfacc]].
      + split; [exact Hbid | left; right; exact Hin].
      + rewrite BlockMapFacts.add_o in Hfacc.
        destruct (BlockMapFacts.eq_dec x.(BlockD.bid) bid) as [Heq | Hneq].
        * injection Hfacc as Hfacc. subst b. split; [exact Heq | left; left; reflexivity].
        * split; [exact Hbid | right; exact Hfacc].
  Qed.

  (* The specification [get_block] needs: a successful lookup's result is
  (a) a member of the blocks indexed, and (b) matches the query id -- the
  same two facts [List.find_some] gave for free before, now proved once
  here instead of ad hoc at every call site. *)
  Lemma build_block_index_sound :
    forall (bs: list BlockD.t) (bid: BlockID.t) (b: BlockD.t),
      BlockMap.find bid (build_block_index bs) = Some b ->
      In b bs /\ b.(BlockD.bid) = bid.
  Proof.
    intros bs bid b Hfind.
    unfold build_block_index in Hfind.
    assert (Hinv0 : forall b', BlockMap.find bid (BlockMap.empty BlockD.t) = Some b' -> b'.(BlockD.bid) = bid).
    { intros b' Hcontra. rewrite BlockMapFacts.empty_o in Hcontra. discriminate. }
    destruct (build_block_index_aux_sound bs (BlockMap.empty BlockD.t) bid b Hinv0 Hfind) as [Hbid [Hin | Hfacc]].
    - split; [exact Hin | exact Hbid].
    - rewrite BlockMapFacts.empty_o in Hfacc. discriminate.
  Qed.

  Lemma get_block_sound :
    forall (f: t) (bid: BlockID.t) (b: BlockD.t),
      get_block f bid = Some b -> In b f.(blocks) /\ b.(BlockD.bid) = bid.
  Proof.
    intros f bid b Hget.
    unfold get_block in Hget.
    rewrite f.(H_block_index) in Hget.
    exact (build_block_index_sound f.(blocks) bid b Hget).
  Qed.

  Definition valid_function (f: t) :=
    forall b,
      In b (blocks f) <-> get_block f b.(BlockD.bid) = Some b.

End CFGFun.


Module CFGProg (D: DIALECT).
  Module CFGFunD := CFGFun(D). (* Required to access Function(D) *)
  Module BlockD := CFGFunD.BlockD.
  Module InstrD := BlockD.InstrD.

  (* Same rationale as [CFGFun.build_block_index]: [get_func] is looked up
  once per function call site across the whole program, so an O(n) scan
  of [functions] is worth replacing with an O(log n) [FuncNameMap] lookup. *)
  Definition build_func_index (fs: list CFGFunD.t) : FuncNameMap.t CFGFunD.t :=
    List.fold_left (fun acc f => FuncNameMap.add f.(CFGFunD.name) f acc) fs (FuncNameMap.empty CFGFunD.t).

  (* A smart contract is a collection of functions and a main function. *)
  Record t : Type := {
    name : string; (* Name of the smart contract *)
    functions : list CFGFunD.t; (* List of functions in the smart contract *)
    main: FuncName.t; (* The main function of the smart contract *)
    func_index : FuncNameMap.t CFGFunD.t; (* built once by [construct] from [functions] *)
    H_func_index : func_index = build_func_index functions (* see H_block_index in CFGFun *)
  }.

  Definition show (p: t) : string :=
    "Contract: " ++ p.(name) ++ "\n" ++
    "Main: " ++ FuncName.show p.(main) ++ "\n" ++
    "Functions: " ++ String.concat "\n" (List.map CFGFunD.show p.(functions)).

  Definition get_func (sc: t) (fname: FuncName.t) : option CFGFunD.t :=
    FuncNameMap.find fname sc.(func_index).

  Definition get_function_names (p: t) : list FuncName.t :=
    List.map (fun f => f.(CFGFunD.name)) p.(functions).

  Definition get_blocks_ids (p: t) (funcname : FuncName.t) : list BlockID.t :=
    match get_func p funcname with
    | Some func => List.map (fun b => b.(BlockD.bid)) func.(CFGFunD.blocks)
    | _ => []
    end.


  Definition construct (name : string) (main: FuncName.t) (functions : list CFGFunD.t) : t :=
    {| name := name; functions := functions; main := main;
       func_index := build_func_index functions; H_func_index := eq_refl |}.

  Lemma build_func_index_aux_sound :
    forall (fs: list CFGFunD.t) (acc: FuncNameMap.t CFGFunD.t) (fname: FuncName.t) (f: CFGFunD.t),
      (forall f', FuncNameMap.find fname acc = Some f' -> f'.(CFGFunD.name) = fname) ->
      FuncNameMap.find fname (List.fold_left (fun a x => FuncNameMap.add x.(CFGFunD.name) x a) fs acc) = Some f ->
      f.(CFGFunD.name) = fname /\ (In f fs \/ FuncNameMap.find fname acc = Some f).
  Proof.
    induction fs as [| x xs IH]; intros acc fname f Hinv Hfind.
    - simpl in Hfind. split.
      + apply Hinv. exact Hfind.
      + right. exact Hfind.
    - simpl in Hfind.
      assert (Hinv' : forall f', FuncNameMap.find fname (FuncNameMap.add x.(CFGFunD.name) x acc) = Some f' -> f'.(CFGFunD.name) = fname).
      { intros f' Hf'.
        rewrite FuncNameMapFacts.add_o in Hf'.
        destruct (FuncNameMapFacts.eq_dec x.(CFGFunD.name) fname) as [Heq | Hneq].
        - injection Hf' as Hf'. subst f'. exact Heq.
        - apply Hinv. exact Hf'.
      }
      destruct (IH (FuncNameMap.add x.(CFGFunD.name) x acc) fname f Hinv' Hfind) as [Hname [Hin | Hfacc]].
      + split; [exact Hname | left; right; exact Hin].
      + rewrite FuncNameMapFacts.add_o in Hfacc.
        destruct (FuncNameMapFacts.eq_dec x.(CFGFunD.name) fname) as [Heq | Hneq].
        * injection Hfacc as Hfacc. subst f. split; [exact Heq | left; left; reflexivity].
        * split; [exact Hname | right; exact Hfacc].
  Qed.

  Lemma build_func_index_sound :
    forall (fs: list CFGFunD.t) (fname: FuncName.t) (f: CFGFunD.t),
      FuncNameMap.find fname (build_func_index fs) = Some f ->
      In f fs /\ f.(CFGFunD.name) = fname.
  Proof.
    intros fs fname f Hfind.
    unfold build_func_index in Hfind.
    assert (Hinv0 : forall f', FuncNameMap.find fname (FuncNameMap.empty CFGFunD.t) = Some f' -> f'.(CFGFunD.name) = fname).
    { intros f' Hcontra. rewrite FuncNameMapFacts.empty_o in Hcontra. discriminate. }
    destruct (build_func_index_aux_sound fs (FuncNameMap.empty CFGFunD.t) fname f Hinv0 Hfind) as [Hname [Hin | Hfacc]].
    - split; [exact Hin | exact Hname].
    - rewrite FuncNameMapFacts.empty_o in Hfacc. discriminate.
  Qed.

  Lemma get_func_sound :
    forall (sc: t) (fname: FuncName.t) (f: CFGFunD.t),
      get_func sc fname = Some f -> In f sc.(functions) /\ f.(CFGFunD.name) = fname.
  Proof.
    intros sc fname f Hget.
    unfold get_func in Hget.
    rewrite sc.(H_func_index) in Hget.
    exact (build_func_index_sound sc.(functions) fname f Hget).
  Qed.

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

      pose proof (get_func_sound p f func E_get_func) as [H_in_func_pfs H_func_name_eq_f].
      pose proof (CFGFunD.get_block_sound func bid b H_get_block) as [H_in_b_funcbs H_b_bid_eq_bid].

      exists func.
      repeat split.
      + apply H_in_func_pfs.
      + apply H_in_b_funcbs.
      + apply FuncName.eqb_eq. exact H_func_name_eq_f.
      + apply BlockID.eqb_eq. exact H_b_bid_eq_bid.

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
