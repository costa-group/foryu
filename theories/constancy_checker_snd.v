Require Import FORYU.state.
Require Import FORYU.program.
Require Import FORYU.semantics.
Require Import FORYU.constancy.
Require Import FORYU.constancy_snd.
Require Import FORYU.list_functions.

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import FSets.FMapFacts.

Module Constancy_checker_snd (D: DIALECT).

  (* [ConstSndD] is projected *out of* [ConstD] (not independently
  instantiated) so that everything below shares one single
  [SmallStep(D)]/[CFGProg(D)] lineage -- see the comment on
  [Constancy]'s own header in constancy.v for why that matters. *)
  Module ConstD := Constancy(D).
  Module ConstSndD := ConstD.ConstSndD.

  Module SmallStepD := ConstD.SmallStepD.
  Module StateD := ConstD.StateD.
  Module CallStackD := ConstD.CallStackD.
  Module StackFrameD := ConstD.StackFrameD.
  Module LocalsD := ConstD.LocalsD.
  Module CFGProgD := ConstD.CFGProgD.
  Module CFGFunD := ConstD.CFGFunD.
  Module BlockD := ConstD.BlockD.
  Module PhiInfoD := ConstD.PhiInfoD.
  Module InstrD := ConstD.InstrD.
  Module ExitInfoD := ConstD.ExitInfoD.
  Module SimpleExprD := ConstD.SimpleExprD.

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

  Module DialectFactsD := DialectFacts(D).
  Module VarMapFacts := FMapFacts.WFacts_fun VarID_legacy_OT VarMap.

  (* [pp_info_snd p fn bid pc pp_info] states that every fact claimed by
  [pp_info] (a checker-computed [pp_const_info_t]) at program point
  [(fn, bid, pc)] is really entailed, in the sense of
  [ConstSndD.const_at_pc] -- the ground-truth relation whose own
  semantic soundness is already established in constancy_snd.v. This
  is the per-program-point soundness notion the whole staged proof
  chains forward (instruction, then block, then function, then whole
  program). *)
  Definition pp_info_snd (p: CFGProgD.t) (fn: FuncName.t) (bid: BlockID.t) (pc: nat) (pp_info: ConstD.pp_const_info_t) : Prop :=
    forall (v: VarID.t) (c: D.value_t),
      VarMap.find v pp_info = Some c ->
      ConstSndD.const_at_pc p fn bid pc v c.

  (* ** [VarMap]/[ConstD.update_const_info]/[ConstD.derive_pairs] plumbing **

  [ConstD.update_const_info m vs pairs] first [VarMap.remove]s every
  variable in [vs] from [m], then [VarMap.add]s every pair in [pairs].
  The lemmas below pin down exactly what [VarMap.find] returns
  afterwards, in the two cases [sym_exec_instr_snd] needs: a variable
  untouched by [vs] (unaffected, carries over from [m]), and a variable
  that [pairs] gives a fresh value for (the newly derived fact). *)

  Lemma fold_left_remove_preserves_none :
    forall (vs: list VarID.t) (m: ConstD.pp_const_info_t) (v: VarID.t),
      VarMap.find v m = None ->
      VarMap.find v (List.fold_left (fun acc v0 => VarMap.remove v0 acc) vs m) = None.
  Proof.
    induction vs as [| v0 vs' IH]; intros m v Hnone.
    - exact Hnone.
    - simpl. apply IH.
      rewrite VarMapFacts.remove_o.
      destruct (VarMapFacts.eq_dec v0 v) as [Heq | Hneq].
      + reflexivity.
      + exact Hnone.
  Qed.

  Lemma fold_left_remove_in :
    forall (vs: list VarID.t) (m: ConstD.pp_const_info_t) (v: VarID.t),
      In v vs ->
      VarMap.find v (List.fold_left (fun acc v0 => VarMap.remove v0 acc) vs m) = None.
  Proof.
    induction vs as [| v0 vs' IH]; intros m v Hin.
    - destruct Hin.
    - simpl. destruct Hin as [Heq | Hin].
      + subst v0.
        apply fold_left_remove_preserves_none.
        rewrite VarMapFacts.remove_o.
        destruct (VarMapFacts.eq_dec v v) as [_ | Hneq]; [reflexivity | exfalso; exact (Hneq eq_refl)].
      + apply IH. exact Hin.
  Qed.

  Lemma fold_left_remove_notin :
    forall (vs: list VarID.t) (m: ConstD.pp_const_info_t) (v: VarID.t),
      ~ In v vs ->
      VarMap.find v (List.fold_left (fun acc v0 => VarMap.remove v0 acc) vs m) = VarMap.find v m.
  Proof.
    induction vs as [| v0 vs' IH]; intros m v Hnotin.
    - reflexivity.
    - simpl.
      assert (Hne : v0 <> v) by (intro Heq; apply Hnotin; left; exact Heq).
      assert (Hnotin' : ~ In v vs') by (intro Hin; apply Hnotin; right; exact Hin).
      rewrite (IH (VarMap.remove v0 m) v Hnotin').
      rewrite VarMapFacts.remove_o.
      destruct (VarMapFacts.eq_dec v0 v) as [Heq | _].
      + exfalso. exact (Hne Heq).
      + reflexivity.
  Qed.

  Lemma fold_left_add_preserves_if_not_in_later :
    forall (pairs: list (VarID.t * D.value_t)) (m': ConstD.pp_const_info_t) (v: VarID.t) (val: D.value_t),
      ~ In v (List.map fst pairs) ->
      VarMap.find v m' = Some val ->
      VarMap.find v (List.fold_left (fun acc p => VarMap.add (fst p) (snd p) acc) pairs m') = Some val.
  Proof.
    induction pairs as [| [v0 val0] pairs' IH]; intros m' v val Hnotin Hfind.
    - exact Hfind.
    - simpl.
      assert (Hne : v0 <> v) by (intro Heq; apply Hnotin; left; exact Heq).
      assert (Hnotin' : ~ In v (List.map fst pairs')) by (intro Hin; apply Hnotin; right; exact Hin).
      apply IH.
      + exact Hnotin'.
      + rewrite VarMapFacts.add_o.
        destruct (VarMapFacts.eq_dec v0 v) as [Heq | _].
        * exfalso. exact (Hne Heq).
        * exact Hfind.
  Qed.

  Lemma fold_left_add_notin :
    forall (pairs: list (VarID.t * D.value_t)) (m': ConstD.pp_const_info_t) (v: VarID.t),
      ~ In v (List.map fst pairs) ->
      VarMap.find v (List.fold_left (fun acc p => VarMap.add (fst p) (snd p) acc) pairs m') = VarMap.find v m'.
  Proof.
    induction pairs as [| [v0 val0] pairs' IH]; intros m' v Hnotin.
    - reflexivity.
    - simpl.
      assert (Hne : v0 <> v) by (intro Heq; apply Hnotin; left; exact Heq).
      assert (Hnotin' : ~ In v (List.map fst pairs')) by (intro Hin; apply Hnotin; right; exact Hin).
      rewrite (IH (VarMap.add v0 val0 m') v Hnotin').
      rewrite VarMapFacts.add_o.
      destruct (VarMapFacts.eq_dec v0 v) as [Heq | _].
      + exfalso. exact (Hne Heq).
      + reflexivity.
  Qed.

  Lemma fold_left_add_in :
    forall (pairs: list (VarID.t * D.value_t)) (m': ConstD.pp_const_info_t) (v: VarID.t) (val: D.value_t),
      In (v, val) pairs ->
      NoDup (List.map fst pairs) ->
      VarMap.find v (List.fold_left (fun acc p => VarMap.add (fst p) (snd p) acc) pairs m') = Some val.
  Proof.
    induction pairs as [| [v0 val0] pairs' IH]; intros m' v val Hin Hnodup.
    - destruct Hin.
    - simpl in Hnodup. inversion Hnodup as [| x0 l0 Hnotin0 Hnodup' Heqlist]; subst.
      destruct Hin as [Heq | Hin].
      + injection Heq as Heq1 Heq2. subst v0 val0.
        simpl.
        apply fold_left_add_preserves_if_not_in_later.
        * exact Hnotin0.
        * rewrite VarMapFacts.add_o.
          destruct (VarMapFacts.eq_dec v v) as [_ | Hneq]; [reflexivity | exfalso; exact (Hneq eq_refl)].
      + simpl. apply IH; assumption.
  Qed.

  (* [derive_pairs vs vals]'s first components are always drawn from
  [vs] itself, in the same order (it is a filtered "zip"), so [vs]'s
  own [NoDup] carries over to it -- needed for [fold_left_add_in]
  above. *)
  Lemma derive_pairs_fst_in_vs :
    forall (vs: list VarID.t) (vals: list (option D.value_t)) (v: VarID.t) (val: D.value_t),
      In (v, val) (ConstD.derive_pairs vs vals) -> In v vs.
  Proof.
    induction vs as [| v0 vs' IH]; intros vals v val Hin.
    - destruct vals; simpl in Hin; destruct Hin.
    - destruct vals as [| [val0|] vals'].
      + simpl in Hin. destruct Hin.
      + simpl in Hin. destruct Hin as [Heq | Hin].
        * injection Heq as Heq1 _. left. exact Heq1.
        * right. exact (IH vals' v val Hin).
      + simpl in Hin. right. exact (IH vals' v val Hin).
  Qed.

  Lemma derive_pairs_nodup :
    forall (vs: list VarID.t) (vals: list (option D.value_t)),
      NoDup vs -> NoDup (List.map fst (ConstD.derive_pairs vs vals)).
  Proof.
    induction vs as [| v0 vs' IH]; intros vals Hnodup.
    - destruct vals; simpl; constructor.
    - inversion Hnodup as [| x0 l0 Hnotin0 Hnodup' Heqlist]; subst.
      destruct vals as [| [val0|] vals'].
      + simpl. constructor.
      + simpl. constructor.
        * intro Hin. apply List.in_map_iff in Hin. destruct Hin as [[v' val'] [Heqfst Hin']].
          simpl in Heqfst. subst v'.
          apply Hnotin0. exact (derive_pairs_fst_in_vs vs' vals' v0 val' Hin').
        * exact (IH vals' Hnodup').
      + simpl. exact (IH vals' Hnodup').
  Qed.

  (* [derive_pairs]'s own index-based characterization: the pair for
  index [k] survives iff the corresponding value did resolve. *)
  Lemma derive_pairs_nth_error_some :
    forall (vs: list VarID.t) (vals: list (option D.value_t)) (k: nat) (v: VarID.t) (val: D.value_t),
      nth_error vs k = Some v ->
      nth_error vals k = Some (Some val) ->
      In (v, val) (ConstD.derive_pairs vs vals).
  Proof.
    induction vs as [| v0 vs' IH]; intros vals k v val Hvs Hvals.
    - destruct k; simpl in Hvs; discriminate.
    - destruct vals as [| val0 vals'].
      + destruct k; simpl in Hvals; discriminate.
      + destruct k as [| k'].
        * simpl in Hvs, Hvals. injection Hvs as Hvs. injection Hvals as Hvals.
          subst v0 val0. left. reflexivity.
        * simpl in Hvs, Hvals.
          destruct val0 as [val0|].
          -- right. exact (IH vals' k' v val Hvs Hvals).
          -- exact (IH vals' k' v val Hvs Hvals).
  Qed.

  (* The converse of [derive_pairs_nth_error_some]: every surviving
  pair does come from some shared index. *)
  Lemma derive_pairs_in_iff_nth_error :
    forall (vs: list VarID.t) (vals: list (option D.value_t)) (v: VarID.t) (val: D.value_t),
      In (v, val) (ConstD.derive_pairs vs vals) ->
      exists k, nth_error vs k = Some v /\ nth_error vals k = Some (Some val).
  Proof.
    induction vs as [| v0 vs' IH]; intros vals v val Hin.
    - destruct vals; simpl in Hin; destruct Hin.
    - destruct vals as [| [val0|] vals'].
      + simpl in Hin. destruct Hin.
      + simpl in Hin. destruct Hin as [Heq | Hin].
        * injection Heq as Heq1 Heq2. subst v0 val0.
          exists 0. split; reflexivity.
        * destruct (IH vals' v val Hin) as [k' [Hk1 Hk2]].
          exists (S k'). split; exact Hk1 || exact Hk2.
      + simpl in Hin.
        destruct (IH vals' v val Hin) as [k' [Hk1 Hk2]].
        exists (S k'). split; exact Hk1 || exact Hk2.
  Qed.

  (* [ListFunctions.option_list]'s own index-based characterization:
  when it succeeds, the resulting list's own [k]-th element is exactly
  whatever the [k]-th input's [Some] carried. *)
  Lemma option_list_nth_error :
    forall (A: Type) (l: list (option A)) (l': list A) (k: nat) (x: A),
      ListFunctions.option_list l = Some l' ->
      nth_error l k = Some (Some x) ->
      nth_error l' k = Some x.
  Proof.
    induction l as [| x0 l0 IH]; intros l' k x Hlist Hnth.
    - destruct k; simpl in Hnth; discriminate.
    - destruct x0 as [x0|].
      + simpl in Hlist.
        destruct (ListFunctions.option_list l0) as [ys|] eqn:Hl0; try discriminate.
        injection Hlist as Hlist. subst l'.
        destruct k as [| k'].
        * simpl in Hnth. injection Hnth as Hnth. subst x0. reflexivity.
        * simpl in Hnth. exact (IH ys k' x eq_refl Hnth).
      + simpl in Hlist. discriminate.
  Qed.

  (* [const_sexprs]'s own soundness (mirrors what used to be
  [const_sexprs_build]) is built directly inside the [CoFixpoint] below,
  as [build_const_sexprs] -- not here as a separate [Lemma] -- because
  its induction over [es] would otherwise be a structural [Fix] applied
  to a *symbolic* (abstract) list once called from inside the guarded
  corecursion, which Coq's guardedness checker cannot see through (it
  only reduces a [Fix] applied to a literal [nil]/[cons], never an
  abstract variable). Folding the recursion into the same mutual
  [CoFixpoint] family instead makes every step of it a genuine
  (recognized, trusted) recursive call, each immediately guarded by a
  real [ConstSndD.const_sexprs_*] constructor. *)

  (* Specialized, direct inductive versions of [List.nth_error_map],
  stated throughout in terms of this file's own [SimpleExprD.t] alias
  rather than a generic type parameter -- [List.nth_error_map] itself
  gets its implicit type argument instantiated from
  [ConstD.eval_sexpr_pp]'s *domain* type, which, though convertible to
  [i.(input)]'s own (intrinsic, [InstrD]-derived) element type, is not
  *syntactically* identical to it; [rewrite] cannot locate an
  occurrence up to conversion alone, only up to (near-)syntactic
  matching. Proving these directly sidesteps the mismatch entirely. *)
  Lemma eval_sexpr_pp_nth_error_some :
    forall (Cb: ConstD.pp_const_info_t) (l: list SimpleExprD.t) (k: nat) (val: D.value_t),
      nth_error (List.map (ConstD.eval_sexpr_pp Cb) l) k = Some (Some val) ->
      exists x, nth_error l k = Some x /\ ConstD.eval_sexpr_pp Cb x = Some val.
  Proof.
    induction l as [| x0 l' IH]; intros k val Hnth.
    - destruct k; simpl in Hnth; discriminate.
    - destruct k as [| k'].
      + simpl in Hnth. injection Hnth as Hnth.
        exists x0. split; [reflexivity | exact Hnth].
      + simpl in Hnth. exact (IH k' val Hnth).
  Qed.

  Lemma map_some_nth_error_some :
    forall (l: list D.value_t) (k: nat) (val: D.value_t),
      nth_error (List.map (fun v0 => Some v0) l) k = Some (Some val) ->
      nth_error l k = Some val.
  Proof.
    induction l as [| x0 l' IH]; intros k val Hnth.
    - destruct k; simpl in Hnth; discriminate.
    - destruct k as [| k'].
      + simpl in Hnth. injection Hnth as Hnth. subst val. reflexivity.
      + simpl in Hnth. exact (IH k' val Hnth).
  Qed.

  (* ** [ConstD.update_const_info]'s own find-characterization, in the
  two shapes [sym_exec_instr_snd] needs it in: with an empty [pairs]
  list (the "nothing derived" fallbacks: function calls, and every
  opcode failure mode), and with a nonempty one (successful
  assign/opcode folding). *)

  Lemma update_const_info_empty_in :
    forall (Cb: ConstD.pp_const_info_t) (vs: list VarID.t) (v: VarID.t),
      In v vs -> VarMap.find v (ConstD.update_const_info Cb vs []) = None.
  Proof.
    intros Cb vs v Hin.
    unfold ConstD.update_const_info. simpl.
    exact (fold_left_remove_in vs Cb v Hin).
  Qed.

  Lemma update_const_info_empty_notin :
    forall (Cb: ConstD.pp_const_info_t) (vs: list VarID.t) (v: VarID.t),
      ~ In v vs -> VarMap.find v (ConstD.update_const_info Cb vs []) = VarMap.find v Cb.
  Proof.
    intros Cb vs v Hnotin.
    unfold ConstD.update_const_info. simpl.
    exact (fold_left_remove_notin vs Cb v Hnotin).
  Qed.

  Lemma update_const_info_in_pairs :
    forall (Cb: ConstD.pp_const_info_t) (vs: list VarID.t) (pairs: list (VarID.t * D.value_t)) (v: VarID.t) (val: D.value_t),
      In (v, val) pairs -> NoDup (List.map fst pairs) ->
      VarMap.find v (ConstD.update_const_info Cb vs pairs) = Some val.
  Proof.
    intros Cb vs pairs v val Hin Hnodup.
    unfold ConstD.update_const_info.
    exact (fold_left_add_in pairs (List.fold_left (fun acc v0 => VarMap.remove v0 acc) vs Cb) v val Hin Hnodup).
  Qed.

  Lemma update_const_info_notin_pairs_in_vs :
    forall (Cb: ConstD.pp_const_info_t) (vs: list VarID.t) (pairs: list (VarID.t * D.value_t)) (v: VarID.t),
      ~ In v (List.map fst pairs) -> In v vs ->
      VarMap.find v (ConstD.update_const_info Cb vs pairs) = None.
  Proof.
    intros Cb vs pairs v HnotinPairs Hin.
    unfold ConstD.update_const_info.
    rewrite (fold_left_add_notin pairs _ v HnotinPairs).
    exact (fold_left_remove_in vs Cb v Hin).
  Qed.

  (* Corollary of [derive_pairs_fst_in_vs]: a variable outside [vs] can
  never be one of [derive_pairs]'s own surviving keys either. *)
  Lemma derive_pairs_notin_vs_notin_fst :
    forall (vs: list VarID.t) (vals: list (option D.value_t)) (v: VarID.t),
      ~ In v vs -> ~ In v (List.map fst (ConstD.derive_pairs vs vals)).
  Proof.
    intros vs vals v Hnotin Hin.
    apply List.in_map_iff in Hin. destruct Hin as [[v' val'] [Heq Hin']].
    simpl in Heq. subst v'.
    exact (Hnotin (derive_pairs_fst_in_vs vs vals v val' Hin')).
  Qed.

  (* Uniform across every instruction kind: a variable that is not one
  of [i]'s outputs is always carried over unchanged from [Cb]. *)
  Lemma sym_exec_instr_unaffected :
    forall (Cb: ConstD.pp_const_info_t) (i: InstrD.t) (v: VarID.t),
      ~ In v i.(output) ->
      VarMap.find v (ConstD.sym_exec_instr i Cb) = VarMap.find v Cb.
  Proof.
    intros Cb i v Hnotin.
    unfold ConstD.sym_exec_instr.
    destruct (i.(InstrD.op)) as [[callee | opcode] | aux] eqn:Hop.
    - exact (update_const_info_empty_notin Cb i.(output) v Hnotin).
    - destruct (ListFunctions.option_list (List.map (ConstD.eval_sexpr_pp Cb) i.(input))) as [concrete_inputs|] eqn:Hoptlist.
      + destruct (D.opcode_indep_state opcode) eqn:Hindep.
        * destruct (D.execute_opcode D.empty_dialect_state opcode concrete_inputs) as [[res_vals st] status] eqn:Hexec.
          destruct status as [ | | | msg] eqn:Hstatus.
          -- unfold ConstD.update_const_info.
             rewrite (fold_left_add_notin _ _ v (derive_pairs_notin_vs_notin_fst i.(output) _ v Hnotin)).
             exact (fold_left_remove_notin i.(output) Cb v Hnotin).
          -- exact (update_const_info_empty_notin Cb i.(output) v Hnotin).
          -- exact (update_const_info_empty_notin Cb i.(output) v Hnotin).
          -- exact (update_const_info_empty_notin Cb i.(output) v Hnotin).
        * exact (update_const_info_empty_notin Cb i.(output) v Hnotin).
      + exact (update_const_info_empty_notin Cb i.(output) v Hnotin).
    - destruct aux.
      unfold ConstD.update_const_info.
      rewrite (fold_left_add_notin _ _ v (derive_pairs_notin_vs_notin_fst i.(output) _ v Hnotin)).
      exact (fold_left_remove_notin i.(output) Cb v Hnotin).
  Qed.

  (* The instruction-level ground truth ([ConstD.sym_exec_instr]/
  [ConstD.check_const_instr]'s soundness) is likewise built directly
  inside the [CoFixpoint] below (as part of [build_pp_info_snd_pc]'s
  own "one more instruction" step), rather than as a separate [Lemma]:
  the final step of that reasoning must end with a *direct* application
  of a real [ConstSndD.const_at_pc_*] constructor, and any separate
  helper [Lemma] wrapping the recursive call, even if [Defined] and
  even with no internal induction of its own, would still make that
  wrapping happen one level of (bare, unguarded) function application
  too late for Coq's guardedness checker to accept. *)

  (* [VarMap.elements]'s own [InA]-based membership characterization
  collapses to plain [In] on pairs here, since [VarID_legacy_OT]'s own
  [eq] is [Logic.eq] (it is backported from the same, [N]-based
  ordered type as [VarID.VarID_as_OT], whose equality is literal
  equality). *)
  Lemma InA_eq_key_elt_in :
    forall (l: list (VarID.t * D.value_t)) (v: VarID.t) (c: D.value_t),
      SetoidList.InA (VarMap.eq_key_elt (elt:=D.value_t)) (v, c) l -> In (v, c) l.
  Proof.
    induction l as [| [v0 c0] l' IH]; intros v c HinA.
    - inversion HinA.
    - inversion HinA as [? ? [Heqk Heqc] Heqp | ? ? Hin' Heqp]; subst.
      + simpl in Heqk. subst v0. simpl in Heqc. subst c0. left. reflexivity.
      + right. exact (IH v c Hin').
  Qed.

  (* [ConstD.const_info_subset]'s own boolean check unfolds to exactly
  the entailment its name promises: everything the first map claims is
  also claimed, identically, by the second. *)
  Lemma const_info_subset_spec :
    forall (m1 m2: ConstD.pp_const_info_t),
      ConstD.const_info_subset m1 m2 = true ->
      forall (v: VarID.t) (c: D.value_t), VarMap.find v m1 = Some c -> VarMap.find v m2 = Some c.
  Proof.
    intros m1 m2 Hsubset v c Hfind.
    unfold ConstD.const_info_subset in Hsubset.
    rewrite List.forallb_forall in Hsubset.
    assert (Hin : In (v, c) (VarMap.elements m1))
      by exact (InA_eq_key_elt_in (VarMap.elements m1) v c (VarMap.elements_1 (VarMap.find_2 Hfind))).
    pose proof (Hsubset (v, c) Hin) as Hcheck.
    simpl in Hcheck.
    destruct (VarMap.find v m2) as [v2|] eqn:Hfind2; try discriminate.
    apply DialectFactsD.eqb_eq in Hcheck. subst v2. reflexivity.
  Qed.

  (* [rev (x :: l)]'s own head, when [l] is non-empty, is unaffected by
  the extra [x] tacked onto the far end. *)
  Lemma hd_error_rev_cons_nonempty :
    forall (A: Type) (x: A) (l: list A),
      l <> [] ->
      List.hd_error (List.rev (x :: l)) = List.hd_error (List.rev l).
  Proof.
    intros A x l Hnonempty.
    simpl.
    destruct (List.rev l) as [| y l'] eqn:Hrev.
    - exfalso. apply Hnonempty. destruct l as [| z l0]; [reflexivity | simpl in Hrev; destruct (List.rev l0); discriminate].
    - reflexivity.
  Qed.

  (* Pure data-level facts about how [ConstD.check_const_pp]'s boolean
  walk over [instrs]/[b_info] relates their positions -- none of these
  mention [pp_info_snd]/the coinductive family at all, so they stay
  ordinary [Qed] lemmas; the actual chaining of [pp_info_snd] facts
  across a block's instructions now happens directly inside the
  [CoFixpoint] below, one instruction at a time, using these purely as
  data-plumbing. *)

  Lemma check_const_pp_length :
    forall (instrs: list InstrD.t) (b_info: ConstD.block_const_info_t),
      ConstD.check_const_pp instrs b_info = true -> length b_info = S (length instrs).
  Proof.
    induction instrs as [| i instrs' IH]; intros b_info Hcheck.
    - destruct b_info as [| Cb0' [| Ca0' rest0]]; simpl in Hcheck; try discriminate.
      reflexivity.
    - destruct b_info as [| Cb [| Ca rest]]; simpl in Hcheck; try discriminate.
      destruct (ConstD.check_const_instr i Cb Ca) eqn:Hinstr; try discriminate.
      simpl. f_equal. exact (IH (Ca :: rest) Hcheck).
  Qed.

  (* Every instruction position [k] (with an actual instruction [i]
  there) has a matching pair of adjacent [b_info] entries validated by
  [ConstD.check_const_instr]. *)
  Lemma check_const_pp_pointwise :
    forall (instrs: list InstrD.t) (b_info: ConstD.block_const_info_t),
      ConstD.check_const_pp instrs b_info = true ->
      forall (k: nat) (i: InstrD.t), nth_error instrs k = Some i ->
      exists (Cb Ca: ConstD.pp_const_info_t),
        nth_error b_info k = Some Cb /\ nth_error b_info (S k) = Some Ca /\
        ConstD.check_const_instr i Cb Ca = true.
  Proof.
    induction instrs as [| i0 instrs' IH]; intros b_info Hcheck k i Hnth.
    - destruct k; simpl in Hnth; discriminate.
    - destruct b_info as [| Cb [| Ca b_info']]; simpl in Hcheck; try discriminate.
      destruct (ConstD.check_const_instr i0 Cb Ca) eqn:Hi0; try discriminate.
      destruct k as [| k'].
      + simpl in Hnth. injection Hnth as Hnth. subst i0.
        exists Cb, Ca. repeat split. exact Hi0.
      + simpl in Hnth.
        destruct (IH (Ca :: b_info') Hcheck k' i Hnth) as [Cb' [Ca' [Hnb [Hna Hchk]]]].
        exists Cb', Ca'. repeat split; [exact Hnb | exact Hna | exact Hchk].
  Qed.

  (* [b_info]'s first and last entries, indexed directly (rather than
  via [hd_error]/[hd_error (rev ...)]), plus the connection back to
  [ConstD.block_exit_info]'s own [hd_error (rev ...)] definition (still
  needed by [check_const_successor_snd]/[ConstD.check_const_edges]). *)
  Lemma check_const_pp_endpoints :
    forall (instrs: list InstrD.t) (b_info: ConstD.block_const_info_t),
      ConstD.check_const_pp instrs b_info = true ->
      exists (Cb0 Cend: ConstD.pp_const_info_t),
        nth_error b_info 0 = Some Cb0 /\
        nth_error b_info (length instrs) = Some Cend /\
        ConstD.block_exit_info b_info = Some Cend.
  Proof.
    induction instrs as [| i instrs' IH]; intros b_info Hcheck.
    - destruct b_info as [| Cb0' [| Ca0' rest0]]; simpl in Hcheck; try discriminate.
      exists Cb0', Cb0'. repeat split; unfold ConstD.block_exit_info; reflexivity.
    - destruct b_info as [| Cb [| Ca rest]]; simpl in Hcheck; try discriminate.
      destruct (ConstD.check_const_instr i Cb Ca) eqn:Hinstr; try discriminate.
      destruct (IH (Ca :: rest) Hcheck) as [Cb0' [Cend' [Hnth0 [Hnthlen Hexit]]]].
      simpl in Hnth0. injection Hnth0 as Hnth0. subst Cb0'.
      exists Cb, Cend'.
      split; [reflexivity | split].
      + simpl. exact Hnthlen.
      + unfold ConstD.block_exit_info in Hexit |- *.
        assert (Hne : Ca :: rest <> []) by discriminate.
        rewrite (hd_error_rev_cons_nonempty _ Cb (Ca :: rest) Hne).
        exact Hexit.
  Qed.

  (* [ConstSndD.phi_source]'s own [List.find]/[List.combine] structure,
  characterized directly by index -- the two directions
  [check_const_successor_snd] needs, mirroring
  [derive_pairs_nth_error_some]/[derive_pairs_notin_vs_notin_fst], but
  for [phi_source]'s "first match" lookup instead of
  [derive_pairs]'s filtered zip. [NoDup vars] is exactly what pins the
  index found down to *the* (unique) occurrence. *)
  Lemma phi_source_from_index :
    forall (vars: list VarID.t) (exprs: list SimpleExprD.t) (v: VarID.t) (k: nat) (e: SimpleExprD.t),
      NoDup vars ->
      nth_error vars k = Some v ->
      nth_error exprs k = Some e ->
      List.find (fun ov => VarID.eqb (fst ov) v) (List.combine vars exprs) = Some (v, e).
  Proof.
    induction vars as [| v0 vars' IH]; intros exprs v k e Hnodup Hv Hex.
    - destruct k; simpl in Hv; discriminate.
    - destruct exprs as [| e0 exprs'].
      + destruct k; simpl in Hex; discriminate.
      + inversion Hnodup as [| x0 l0 Hnotin0 Hnodup' Heqlist]; subst.
        destruct k as [| k'].
        * simpl in Hv, Hex. injection Hv as Hv. injection Hex as Hex. subst v0 e0.
          simpl. rewrite VarID.eqb_refl. reflexivity.
        * simpl in Hv, Hex. simpl.
          assert (Hne : v0 <> v)
            by (intro Heq; subst v0; exact (Hnotin0 (List.nth_error_In vars' k' Hv))).
          rewrite (proj2 (VarID.eqb_neq_false v0 v) Hne).
          exact (IH exprs' v k' e Hnodup' Hv Hex).
  Qed.

  Lemma phi_source_notin_find_none :
    forall (vars: list VarID.t) (exprs: list SimpleExprD.t) (v: VarID.t),
      ~ In v vars ->
      List.find (fun ov => VarID.eqb (fst ov) v) (List.combine vars exprs) = None.
  Proof.
    induction vars as [| v0 vars' IH]; intros exprs v Hnotin.
    - reflexivity.
    - destruct exprs as [| e0 exprs'].
      + reflexivity.
      + simpl.
        assert (Hne : v0 <> v) by (intro Heq; apply Hnotin; left; exact Heq).
        assert (Hnotin' : ~ In v vars') by (intro Hin; apply Hnotin; right; exact Hin).
        rewrite (proj2 (VarID.eqb_neq_false v0 v) Hne).
        exact (IH exprs' v Hnotin').
  Qed.

  (* Checking one predecessor edge is sound: everything the successor
  block's claimed entry info states is entailed by [ConstSndD.const_in]'s
  own per-predecessor obligation (the phi-transferred/carried-over
  value of [pred_exit], which is itself known-sound). *)
  Lemma check_const_successor_snd :
    forall (p: CFGProgD.t) (f_info: ConstD.func_const_info_t) (fname: FuncName.t) (pred_bid: BlockID.t) (pred_b: BlockD.t) (pred_exit: ConstD.pp_const_info_t) (next_bid: BlockID.t),
      CFGProgD.get_block p fname pred_bid = Some pred_b ->
      ConstD.check_const_successor p f_info fname pred_bid pred_exit next_bid = true ->
      pp_info_snd p fname pred_bid (length pred_b.(instructions)) pred_exit ->
      forall (next_b: BlockD.t) (next_b_info: ConstD.block_const_info_t) (next_entry: ConstD.pp_const_info_t),
        CFGProgD.get_block p fname next_bid = Some next_b ->
        f_info next_bid = Some next_b_info ->
        ConstD.block_entry_info next_b_info = Some next_entry ->
        forall (v: VarID.t) (c: D.value_t), VarMap.find v next_entry = Some c ->
          (ConstSndD.phi_source next_b pred_bid v = None /\ ConstSndD.const_out p fname pred_bid v c)
          \/ (exists v', ConstSndD.phi_source next_b pred_bid v = Some (inl v') /\ ConstSndD.const_out p fname pred_bid v' c)
          \/ (exists val, ConstSndD.phi_source next_b pred_bid v = Some (inr val) /\ c = val).
  Proof.
    intros p f_info fname pred_bid pred_b pred_exit next_bid Hpredblock Hcheck Hsnd
           next_b next_b_info next_entry Hnextblock Hfinfo Hentry v c Hfind.
    unfold ConstD.check_const_successor in Hcheck.
    rewrite Hnextblock, Hfinfo, Hentry in Hcheck.
    destruct (snd next_b.(phi_function) pred_bid) as [in_sexprs] eqn:Hphi.
    assert (Hfind' : VarMap.find v (ConstD.update_const_info pred_exit (fst next_b.(phi_function))
                         (ConstD.derive_pairs (fst next_b.(phi_function)) (List.map (ConstD.eval_sexpr_pp pred_exit) in_sexprs))) = Some c)
      by exact (const_info_subset_spec next_entry _ Hcheck v c Hfind).
    unfold ConstSndD.phi_source.
    rewrite Hphi.
    destruct (List.in_dec VarMapFacts.eq_dec v (fst next_b.(phi_function))) as [Hin | Hnotin].
    - destruct (List.in_dec VarMapFacts.eq_dec v (List.map fst (ConstD.derive_pairs (fst next_b.(phi_function)) (List.map (ConstD.eval_sexpr_pp pred_exit) in_sexprs)))) as [HinPairs | HnotinPairs].
      + apply List.in_map_iff in HinPairs. destruct HinPairs as [[v' val'] [Heqfst HinPairs']].
        simpl in Heqfst. subst v'.
        rewrite (update_const_info_in_pairs pred_exit (fst next_b.(phi_function)) _ v val' HinPairs'
                   (derive_pairs_nodup (fst next_b.(phi_function)) _ next_b.(BlockD.H_phi_nodup))) in Hfind'.
        injection Hfind' as Hfind'. subst val'.
        destruct (derive_pairs_in_iff_nth_error (fst next_b.(phi_function)) (List.map (ConstD.eval_sexpr_pp pred_exit) in_sexprs) v c HinPairs') as [k [Hk1 Hk2]].
        assert (Hx : exists x, nth_error in_sexprs k = Some x /\ ConstD.eval_sexpr_pp pred_exit x = Some c)
          by exact (eval_sexpr_pp_nth_error_some pred_exit in_sexprs k c Hk2).
        destruct Hx as [x [Hxeq Hevalx]].
        assert (Hfindphi : List.find (fun ov => VarID.eqb (fst ov) v) (List.combine (fst next_b.(phi_function)) in_sexprs) = Some (v, x))
          by exact (phi_source_from_index (fst next_b.(phi_function)) in_sexprs v k x next_b.(BlockD.H_phi_nodup) Hk1 Hxeq).
        rewrite Hfindphi.
        destruct x as [v'' | val].
        * right. left. exists v''. split; [reflexivity | ].
          simpl in Hevalx.
          exact (ConstSndD.const_out_any p fname pred_bid pred_b v'' c Hpredblock (Hsnd v'' c Hevalx)).
        * right. right. exists val. split; [reflexivity | ].
          simpl in Hevalx. injection Hevalx as Hevalx. exact (eq_sym Hevalx).
      + exfalso.
        rewrite (update_const_info_notin_pairs_in_vs pred_exit (fst next_b.(phi_function)) _ v HnotinPairs Hin) in Hfind'.
        discriminate Hfind'.
    - assert (Heq2 : VarMap.find v (ConstD.update_const_info pred_exit (fst next_b.(phi_function))
                         (ConstD.derive_pairs (fst next_b.(phi_function)) (List.map (ConstD.eval_sexpr_pp pred_exit) in_sexprs))) = VarMap.find v pred_exit).
      { unfold ConstD.update_const_info.
        rewrite (fold_left_add_notin _ _ v (derive_pairs_notin_vs_notin_fst (fst next_b.(phi_function)) _ v Hnotin)).
        exact (fold_left_remove_notin (fst next_b.(phi_function)) pred_exit v Hnotin). }
      rewrite Heq2 in Hfind'.
      assert (Hfindphi_none : List.find (fun ov => VarID.eqb (fst ov) v) (List.combine (fst next_b.(phi_function)) in_sexprs) = None)
        by exact (phi_source_notin_find_none (fst next_b.(phi_function)) in_sexprs v Hnotin).
      rewrite Hfindphi_none.
      left. split; [reflexivity | ].
      exact (ConstSndD.const_out_any p fname pred_bid pred_b v c Hpredblock (Hsnd v c Hfind')).
  Defined.

  (* ** Wiring the whole-program checker down to a specific block **

  [CFGProgD.get_func]/[CFGFunD.get_block] both resolve via
  [List.find], so a successful lookup's own result is (a) a member of
  the list searched, and (b) matches the query on the field being
  compared. *)
  Lemma get_func_in :
    forall (p: CFGProgD.t) (fn: FuncName.t) (f: CFGFunD.t),
      CFGProgD.get_func p fn = Some f -> In f p.(functions).
  Proof.
    intros p fn f Hget.
    unfold CFGProgD.get_func in Hget.
    destruct (List.find (fun f0 => FuncName.eqb f0.(CFGFunD.name) fn) p.(functions)) as [f'|] eqn:Hfind; try discriminate.
    injection Hget as Hget. subst f'.
    exact (proj1 (List.find_some _ _ Hfind)).
  Qed.

  Lemma get_func_name_eq :
    forall (p: CFGProgD.t) (fn: FuncName.t) (f: CFGFunD.t),
      CFGProgD.get_func p fn = Some f -> f.(CFGFunD.name) = fn.
  Proof.
    intros p fn f Hget.
    unfold CFGProgD.get_func in Hget.
    destruct (List.find (fun f0 => FuncName.eqb f0.(CFGFunD.name) fn) p.(functions)) as [f'|] eqn:Hfind; try discriminate.
    injection Hget as Hget. subst f'.
    apply FuncName.eqb_eq. exact (proj2 (List.find_some _ _ Hfind)).
  Qed.

  Lemma get_block_in :
    forall (p: CFGProgD.t) (fn: FuncName.t) (bid: BlockID.t) (f: CFGFunD.t) (b: BlockD.t),
      CFGProgD.get_func p fn = Some f ->
      CFGProgD.get_block p fn bid = Some b -> In b f.(blocks).
  Proof.
    intros p fn bid f b Hgetf Hgetb.
    unfold CFGProgD.get_block in Hgetb.
    rewrite Hgetf in Hgetb.
    unfold CFGFunD.get_block in Hgetb.
    destruct (List.find (fun b0 => BlockID.eqb b0.(BlockD.bid) bid) f.(blocks)) as [b'|] eqn:Hfind; try discriminate.
    injection Hgetb as Hgetb. subst b'.
    exact (proj1 (List.find_some _ _ Hfind)).
  Qed.

  Lemma get_block_bid_eq :
    forall (p: CFGProgD.t) (fn: FuncName.t) (bid: BlockID.t) (f: CFGFunD.t) (b: BlockD.t),
      CFGProgD.get_func p fn = Some f ->
      CFGProgD.get_block p fn bid = Some b -> b.(BlockD.bid) = bid.
  Proof.
    intros p fn bid f b Hgetf Hgetb.
    unfold CFGProgD.get_block in Hgetb.
    rewrite Hgetf in Hgetb.
    unfold CFGFunD.get_block in Hgetb.
    destruct (List.find (fun b0 => BlockID.eqb b0.(BlockD.bid) bid) f.(blocks)) as [b'|] eqn:Hfind; try discriminate.
    injection Hgetb as Hgetb. subst b'.
    apply BlockID.eqb_eq. exact (proj2 (List.find_some _ _ Hfind)).
  Qed.

  Lemma check_const_functions_snd :
    forall (fs: list CFGFunD.t) (p: CFGProgD.t) (r: ConstD.prog_const_info_t),
      ConstD.check_const_functions fs p r = true ->
      forall (f: CFGFunD.t), In f fs -> ConstD.check_const_blocks f.(blocks) f p r = true.
  Proof.
    induction fs as [| f0 fs' IH]; intros p r Hcheck f Hin.
    - destruct Hin.
    - simpl in Hcheck. destruct (ConstD.check_const_blocks f0.(blocks) f0 p r) eqn:Hb0; try discriminate.
      destruct Hin as [Heq | Hin].
      + subst f0. exact Hb0.
      + exact (IH p r Hcheck f Hin).
  Qed.

  Lemma check_const_blocks_snd :
    forall (bs: list BlockD.t) (f: CFGFunD.t) (p: CFGProgD.t) (r: ConstD.prog_const_info_t),
      ConstD.check_const_blocks bs f p r = true ->
      forall (b: BlockD.t), In b bs ->
        exists (f_info: ConstD.func_const_info_t) (b_info: ConstD.block_const_info_t),
          r f.(CFGFunD.name) = Some f_info /\ f_info b.(BlockD.bid) = Some b_info /\
          ConstD.check_const_pp b.(instructions) b_info = true /\
          ConstD.check_const_edges p f_info f.(CFGFunD.name) b b_info = true /\
          ConstD.check_const_entry f b b_info = true.
  Proof.
    induction bs as [| b0 bs' IH]; intros f p r Hcheck b Hin.
    - destruct Hin.
    - simpl in Hcheck.
      destruct (r f.(CFGFunD.name)) as [f_info|] eqn:Hr; try discriminate.
      destruct (f_info b0.(BlockD.bid)) as [b_info|] eqn:Hb0info; try discriminate.
      destruct (andb (andb (ConstD.check_const_pp b0.(instructions) b_info) (ConstD.check_const_edges p f_info f.(CFGFunD.name) b0 b_info)) (ConstD.check_const_entry f b0 b_info)) eqn:Hb0checks; try discriminate.
      destruct Hin as [Heq | Hin].
      + subst b0.
        exists f_info, b_info.
        apply andb_true_iff in Hb0checks. destruct Hb0checks as [Hb0checks Hentry].
        apply andb_true_iff in Hb0checks. destruct Hb0checks as [Hpp Hedges].
        repeat split; assumption.
      + rewrite <- Hr. exact (IH f p r Hcheck b Hin).
  Qed.

  (* The one-stop extraction lemma: from [check_const_program p r =
  true] and a specific, reachable [(fn, bid)], pull out exactly the
  local facts the checker validated there. *)
  Lemma check_const_program_block_snd :
    forall (p: CFGProgD.t) (r: ConstD.prog_const_info_t),
      ConstD.check_const_program p r = true ->
      forall (fn: FuncName.t) (bid: BlockID.t) (f: CFGFunD.t) (b: BlockD.t),
        CFGProgD.get_func p fn = Some f ->
        CFGProgD.get_block p fn bid = Some b ->
        exists (f_info: ConstD.func_const_info_t) (b_info: ConstD.block_const_info_t),
          r fn = Some f_info /\ f_info bid = Some b_info /\
          ConstD.check_const_pp b.(instructions) b_info = true /\
          ConstD.check_const_edges p f_info fn b b_info = true /\
          ConstD.check_const_entry f b b_info = true.
  Proof.
    intros p r Hcheck fn bid f b Hgetf Hgetb.
    unfold ConstD.check_const_program in Hcheck.
    pose proof (check_const_functions_snd p.(functions) p r Hcheck f (get_func_in p fn f Hgetf)) as Hcheckf.
    pose proof (check_const_blocks_snd f.(blocks) f p r Hcheckf b (get_block_in p fn bid f b Hgetf Hgetb)) as Hcheckb.
    rewrite (get_func_name_eq p fn f Hgetf), (get_block_bid_eq p fn bid f b Hgetf Hgetb) in Hcheckb.
    exact Hcheckb.
  Qed.

  (* [VarMap.is_empty]'s own characterization: an empty map's [find]
  is always [None]. *)
  Lemma varmap_is_empty_find_none :
    forall (m: ConstD.pp_const_info_t) (v: VarID.t),
      VarMap.is_empty m = true -> VarMap.find v m = None.
  Proof.
    intros m v Hempty.
    destruct (VarMap.find v m) as [c|] eqn:Hfind; [exfalso | reflexivity].
    apply VarMap.find_2 in Hfind.
    apply (VarMap.is_empty_2 Hempty) in Hfind.
    exact Hfind.
  Qed.

  (* ** The coinductive core **

  [build_pp_info_snd_pc] builds the actual [ConstSndD.const_in]/
  [const_out]/[const_at_pc] proof terms (via [pp_info_snd] at an
  arbitrary program point [pc] of a block) that the checker-validated
  [r] is entitled to claim -- productively, since the CFG may loop,
  exactly mirroring why [const_in]/[const_out]/[const_at_pc]/
  [const_sexprs] are themselves coinductive.

  Unlike an earlier attempt at this proof, the within-block, entry-to-
  exit propagation (what used to be a separate [check_const_pp_snd]
  [Lemma], proven by [induction] over the block's own, here abstract/
  symbolic instruction list) is *not* a separate [Lemma] at all: Coq's
  guardedness checker can verify a recursive call is safe only when it
  is a direct argument to a real coinductive constructor -- possibly
  after unfolding a *transparent, non-recursive* helper that itself
  ends by applying such a constructor (as [check_const_successor_snd]
  below does) -- but it can never see through a [Fix]/[induction]
  applied to a list it cannot reduce (an arbitrary, universally
  quantified block's instructions), no matter how the wrapping is
  arranged. The fix is to fold that within-block recursion (on [pc],
  one instruction at a time) directly into this same mutual
  [CoFixpoint] family, alongside [build_const_sexprs] (needed for the
  opcode case, for the same reason [const_sexprs_build] could not stay
  a separate [Lemma] either): a call from one family member to another
  is trusted outright (never unfolded/reduced) by the guardedness
  checker, as long as the call itself sits directly under a real
  constructor at its own occurrence -- which is exactly how every step
  below is arranged. *)
  CoFixpoint build_pp_info_snd_pc
    (p: CFGProgD.t) (r: ConstD.prog_const_info_t) (Hcheck: ConstD.check_const_program p r = true)
    (fn: FuncName.t) (at_bid: BlockID.t) (f: CFGFunD.t) (b: BlockD.t)
    (f_info: ConstD.func_const_info_t) (b_info: ConstD.block_const_info_t)
    (Hgetf: CFGProgD.get_func p fn = Some f) (Hgetb: CFGProgD.get_block p fn at_bid = Some b)
    (Hrf: r fn = Some f_info) (Hfb: f_info at_bid = Some b_info)
    (Hpp: ConstD.check_const_pp b.(instructions) b_info = true)
    (Hedges: ConstD.check_const_edges p f_info fn b b_info = true)
    (Hentry_chk: ConstD.check_const_entry f b b_info = true)
    (pc: nat) (C: ConstD.pp_const_info_t) (HC: List.nth_error b_info pc = Some C)
    : pp_info_snd p fn at_bid pc C
  with build_const_sexprs
    (p: CFGProgD.t) (r: ConstD.prog_const_info_t) (Hcheck: ConstD.check_const_program p r = true)
    (fn: FuncName.t) (at_bid: BlockID.t) (f: CFGFunD.t) (b: BlockD.t)
    (f_info: ConstD.func_const_info_t) (b_info: ConstD.block_const_info_t)
    (Hgetf: CFGProgD.get_func p fn = Some f) (Hgetb: CFGProgD.get_block p fn at_bid = Some b)
    (Hrf: r fn = Some f_info) (Hfb: f_info at_bid = Some b_info)
    (Hpp: ConstD.check_const_pp b.(instructions) b_info = true)
    (Hedges: ConstD.check_const_edges p f_info fn b b_info = true)
    (Hentry_chk: ConstD.check_const_entry f b b_info = true)
    (pc: nat) (Cb: ConstD.pp_const_info_t) (HCb: List.nth_error b_info pc = Some Cb)
    (es: list SimpleExprD.t) (cs: list D.value_t)
    (Hlist: ListFunctions.option_list (List.map (ConstD.eval_sexpr_pp Cb) es) = Some cs)
    : ConstSndD.const_sexprs p fn at_bid pc es cs.
  Proof.
    - (* build_pp_info_snd_pc *)
      destruct pc as [| pc'].
      + (* pc = 0: entry soundness -- either the function's own entry
        (vacuous, since empty), or built from every predecessor's own
        exit soundness. Same content as the former, separate
        [build_pp_info_snd_entry], just reached via [HC] instead of a
        [block_entry_info] hypothesis. *)
        assert (Hentry : ConstD.block_entry_info b_info = Some C).
        { unfold ConstD.block_entry_info.
          destruct b_info as [| x l]; simpl in HC.
          - discriminate.
          - injection HC as HC. subst x. reflexivity. }
        clear HC.
        unfold ConstD.check_const_entry in Hentry_chk.
        destruct (BlockID.eqb b.(BlockD.bid) f.(entry_bid)) eqn:Hbideq.
        * (* b is f's own entry block: C is empty, so pp_info_snd holds vacuously *)
          rewrite Hentry in Hentry_chk.
          intros v c Hfind.
          exfalso.
          rewrite (varmap_is_empty_find_none C v Hentry_chk) in Hfind.
          discriminate Hfind.
        * (* b is not f's own entry: build const_in via every predecessor *)
          intros v c Hfind.
          apply ConstSndD.const_at_pc_entry.
          assert (Hne : at_bid <> f.(entry_bid)).
          { intro Heq. apply BlockID.eqb_neq_false in Hbideq.
            assert (Hbid_eq : b.(BlockD.bid) = at_bid) by exact (get_block_bid_eq p fn at_bid f b Hgetf Hgetb).
            rewrite Hbid_eq in Hbideq. exact (Hbideq Heq). }
          apply (ConstSndD.const_in_merge p fn f at_bid b v c Hgetf Hne Hgetb b.(BlockD.H_phi_nodup)).
          intros pred_bid pred_b Hispred.
          destruct Hispred as [Hpredblock Hexit_match].
          destruct (check_const_program_block_snd p r Hcheck fn pred_bid f pred_b Hgetf Hpredblock)
            as [pred_f_info [pred_b_info [Hpred_rf [Hpred_fb [Hpred_pp [Hpred_edges Hpred_entry_chk]]]]]].
          destruct (check_const_pp_endpoints pred_b.(instructions) pred_b_info Hpred_pp)
            as [pred_Cb0 [pred_Cend [Hpred_hd0 [Hpred_hdlen Hpred_exit_eq]]]].
          assert (Hpred_exit_snd : pp_info_snd p fn pred_bid (length pred_b.(instructions)) pred_Cend)
            by exact (build_pp_info_snd_pc p r Hcheck fn pred_bid f pred_b pred_f_info pred_b_info
                        Hgetf Hpredblock Hpred_rf Hpred_fb Hpred_pp Hpred_edges Hpred_entry_chk
                        (length pred_b.(instructions)) pred_Cend Hpred_hdlen).
          assert (Heq_f_info : pred_f_info = f_info)
            by (rewrite Hrf in Hpred_rf; injection Hpred_rf as Hpred_rf; exact (eq_sym Hpred_rf)).
          subst pred_f_info.
          assert (Hpredbid_eq : pred_b.(BlockD.bid) = pred_bid)
            by exact (get_block_bid_eq p fn pred_bid f pred_b Hgetf Hpredblock).
          assert (Hedges_pred : ConstD.check_const_successor p f_info fn pred_bid pred_Cend at_bid = true).
          { unfold ConstD.check_const_edges in Hpred_edges.
            rewrite Hpred_exit_eq in Hpred_edges.
            destruct (pred_b.(exit_info)) as [cond_var nt nf | nj | rs | ] eqn:Hpred_exit_info.
            - simpl in Hexit_match.
              destruct Hexit_match as [Heq | Heq].
              + subst nt. apply andb_true_iff in Hpred_edges. rewrite Hpredbid_eq in Hpred_edges. exact (proj1 Hpred_edges).
              + subst nf. apply andb_true_iff in Hpred_edges. rewrite Hpredbid_eq in Hpred_edges. exact (proj2 Hpred_edges).
            - simpl in Hexit_match. subst nj. rewrite Hpredbid_eq in Hpred_edges. exact Hpred_edges.
            - destruct Hexit_match.
            - destruct Hexit_match.
          }
          exact (check_const_successor_snd p f_info fn pred_bid pred_b pred_Cend at_bid
                   Hpredblock Hedges_pred Hpred_exit_snd
                   b b_info C Hgetb Hfb Hentry v c Hfind).
      + (* pc = S pc': one more instruction step, propagated from [pc'].
        Inlines what used to be [sym_exec_instr_snd]/[check_const_instr_snd],
        using the recursive call [build_pp_info_snd_pc ... pc' ...] in
        place of an externally-supplied hypothesis, and the sibling
        [build_const_sexprs] in place of [const_sexprs_build] -- every
        branch below ends by directly applying a real
        [ConstSndD.const_at_pc_*] constructor. *)
        destruct (nth_error b.(instructions) pc') as [i|] eqn:Hnthi.
        * destruct (check_const_pp_pointwise b.(instructions) b_info Hpp pc' i Hnthi)
            as [Cb [Ca [HnthCb [HnthCa Hchecki]]]].
          assert (Heq : Ca = C) by (rewrite HnthCa in HC; injection HC as HC; exact HC).
          subst Ca.
          assert (Hsnd_pc' : pp_info_snd p fn at_bid pc' Cb)
            by exact (build_pp_info_snd_pc p r Hcheck fn at_bid f b f_info b_info
                        Hgetf Hgetb Hrf Hfb Hpp Hedges Hentry_chk pc' Cb HnthCb).
          unfold ConstD.check_const_instr in Hchecki.
          intros v c Hfind.
          assert (Hfind' : VarMap.find v (ConstD.sym_exec_instr i Cb) = Some c)
            by exact (const_info_subset_spec C (ConstD.sym_exec_instr i Cb) Hchecki v c Hfind).
          destruct (List.in_dec VarMapFacts.eq_dec v i.(output)) as [Hin | Hnotin].
          -- unfold ConstD.sym_exec_instr in Hfind'.
             destruct (i.(InstrD.op)) as [[callee | opcode] | aux] eqn:Hop.
             ++ exfalso. rewrite (update_const_info_empty_in Cb i.(output) v Hin) in Hfind'. discriminate Hfind'.
             ++ destruct (ListFunctions.option_list (List.map (ConstD.eval_sexpr_pp Cb) i.(input))) as [concrete_inputs|] eqn:Hoptlist.
                ** destruct (D.opcode_indep_state opcode) eqn:Hindep.
                   --- destruct (D.execute_opcode D.empty_dialect_state opcode concrete_inputs) as [[res_vals st] status] eqn:Hexec.
                       destruct status as [ | | | msg] eqn:Hstatus.
                       +++ destruct (List.in_dec VarMapFacts.eq_dec v (List.map fst (ConstD.derive_pairs i.(output) (List.map (fun v0 => Some v0) res_vals)))) as [HinPairs | HnotinPairs].
                           *** apply List.in_map_iff in HinPairs. destruct HinPairs as [[v' val'] [Heqfst HinPairs']].
                               simpl in Heqfst. subst v'.
                               rewrite (update_const_info_in_pairs Cb i.(output) _ v val' HinPairs'
                                          (derive_pairs_nodup i.(output) _ i.(InstrD.H_nodup))) in Hfind'.
                               injection Hfind' as Hfind'. subst val'.
                               destruct (derive_pairs_in_iff_nth_error i.(output) (List.map (fun v0 => Some v0) res_vals) v c HinPairs') as [k [Hk1 Hk2]].
                               assert (Hres : nth_error res_vals k = Some c)
                                 by exact (map_some_nth_error_some res_vals k c Hk2).
                               exact (ConstSndD.const_at_pc_opcode p fn at_bid pc' b i opcode v c k concrete_inputs res_vals st
                                        Hgetb Hnthi Hop Hindep
                                        (build_const_sexprs p r Hcheck fn at_bid f b f_info b_info
                                           Hgetf Hgetb Hrf Hfb Hpp Hedges Hentry_chk pc' Cb HnthCb
                                           i.(input) concrete_inputs Hoptlist)
                                        Hexec Hk1 Hres).
                           *** exfalso.
                               rewrite (update_const_info_notin_pairs_in_vs Cb i.(output) _ v HnotinPairs Hin) in Hfind'.
                               discriminate Hfind'.
                       +++ exfalso. rewrite (update_const_info_empty_in Cb i.(output) v Hin) in Hfind'. discriminate Hfind'.
                       +++ exfalso. rewrite (update_const_info_empty_in Cb i.(output) v Hin) in Hfind'. discriminate Hfind'.
                       +++ exfalso. rewrite (update_const_info_empty_in Cb i.(output) v Hin) in Hfind'. discriminate Hfind'.
                   --- exfalso. rewrite (update_const_info_empty_in Cb i.(output) v Hin) in Hfind'. discriminate Hfind'.
                ** exfalso. rewrite (update_const_info_empty_in Cb i.(output) v Hin) in Hfind'. discriminate Hfind'.
             ++ destruct aux.
                destruct (List.in_dec VarMapFacts.eq_dec v (List.map fst (ConstD.derive_pairs i.(output) (List.map (ConstD.eval_sexpr_pp Cb) i.(input))))) as [HinPairs | HnotinPairs].
                ** apply List.in_map_iff in HinPairs. destruct HinPairs as [[v' val'] [Heqfst HinPairs']].
                   simpl in Heqfst. subst v'.
                   rewrite (update_const_info_in_pairs Cb i.(output) _ v val' HinPairs'
                              (derive_pairs_nodup i.(output) _ i.(InstrD.H_nodup))) in Hfind'.
                   injection Hfind' as Hfind'. subst val'.
                   destruct (derive_pairs_in_iff_nth_error i.(output) (List.map (ConstD.eval_sexpr_pp Cb) i.(input)) v c HinPairs') as [k [Hk1 Hk2]].
                   assert (Hx : exists x, nth_error i.(input) k = Some x /\ ConstD.eval_sexpr_pp Cb x = Some c)
                     by exact (eval_sexpr_pp_nth_error_some Cb i.(input) k c Hk2).
                   destruct Hx as [x [Hxeq Hevalx]].
                   assert (Hdisj : (exists v', x = inl v' /\ ConstSndD.const_at_pc p fn at_bid pc' v' c) \/ (exists val, x = inr val /\ c = val)).
                   { destruct x as [v'|val].
                     - left. exists v'. split; [reflexivity | ]. simpl in Hevalx. exact (Hsnd_pc' v' c Hevalx).
                     - right. exists val. split; [reflexivity | ]. simpl in Hevalx. injection Hevalx as Hevalx. exact (eq_sym Hevalx). }
                   exact (ConstSndD.const_at_pc_assign p fn at_bid pc' b i v c k x Hgetb Hnthi Hop Hk1 Hxeq Hdisj).
                ** exfalso.
                   rewrite (update_const_info_notin_pairs_in_vs Cb i.(output) _ v HnotinPairs Hin) in Hfind'.
                   discriminate Hfind'.
          -- rewrite (sym_exec_instr_unaffected Cb i v Hnotin) in Hfind'.
             exact (ConstSndD.const_at_pc_unaffected p fn at_bid pc' b i v c Hgetb Hnthi Hnotin (Hsnd_pc' v c Hfind')).
        * (* nth_error b.(instructions) pc' = None: impossible, since
          [HC] places [C] at position [S pc'] of [b_info], whose length
          is exactly one more than [b.(instructions)]'s own. *)
          exfalso.
          assert (Hlen : length b_info = S (length b.(instructions)))
            by exact (check_const_pp_length b.(instructions) b_info Hpp).
          assert (Hnotnone : nth_error b_info (S pc') <> None) by (rewrite HC; discriminate).
          apply List.nth_error_Some in Hnotnone.
          rewrite Hlen in Hnotnone.
          apply List.nth_error_None in Hnthi.
          lia.
    - (* build_const_sexprs: ordinary structural recursion over [es],
      expressed directly as part of this mutual family (rather than a
      separate [Lemma]) so that a use of it from within
      [build_pp_info_snd_pc]'s opcode case stays a trusted, un-unfolded
      recursive call instead of a [Fix] Coq's checker would get stuck
      trying to reduce on a symbolic list. Note it takes no
      pre-computed [pp_info_snd] fact as a parameter -- only the same
      plain data [build_pp_info_snd_pc] itself was given -- and calls
      [build_pp_info_snd_pc] again, internally, whenever it needs one:
      passing a value *already derived from* one recursive/mutual call
      as a bare argument *into* another is rejected outright by Coq's
      guardedness checker ("Nested recursive occurrences"), even when
      the outer call is itself directly wrapped by a real constructor
      afterwards, and even when the inner call is fully applied first.
      Calling [build_pp_info_snd_pc] from *inside* this member's own
      body instead avoids that nesting entirely. *)
      destruct es as [| x es'].
      + simpl in Hlist. injection Hlist as Hlist. subst cs.
        exact (ConstSndD.const_sexprs_nil p fn at_bid pc).
      + destruct x as [v | val].
        * simpl in Hlist.
          destruct (VarMap.find v Cb) as [val|] eqn:Hfind; try discriminate.
          destruct (ListFunctions.option_list (List.map (ConstD.eval_sexpr_pp Cb) es')) as [cs'|] eqn:Hlist'; try discriminate.
          injection Hlist as Hlist. subst cs.
          exact (ConstSndD.const_sexprs_cons_var p fn at_bid pc v val es' cs'
                   (build_pp_info_snd_pc p r Hcheck fn at_bid f b f_info b_info
                      Hgetf Hgetb Hrf Hfb Hpp Hedges Hentry_chk pc Cb HCb v val Hfind)
                   (build_const_sexprs p r Hcheck fn at_bid f b f_info b_info
                      Hgetf Hgetb Hrf Hfb Hpp Hedges Hentry_chk pc Cb HCb es' cs' Hlist')).
        * simpl in Hlist.
          destruct (ListFunctions.option_list (List.map (ConstD.eval_sexpr_pp Cb) es')) as [cs'|] eqn:Hlist'; try discriminate.
          injection Hlist as Hlist. subst cs.
          exact (ConstSndD.const_sexprs_cons_val p fn at_bid pc val es' cs'
                   (build_const_sexprs p r Hcheck fn at_bid f b f_info b_info
                      Hgetf Hgetb Hrf Hfb Hpp Hedges Hentry_chk pc Cb HCb es' cs' Hlist')).
  Defined.

  (* Soundness of the boolean constancy checker: whatever a
  checker-validated result [r] claims about a program point is really
  true of it, in the sense of [ConstSndD.const_at_pc] -- the same
  ground-truth relation whose own semantic soundness (w.r.t. actual
  program execution) is proven in constancy_snd.v. Composing the two
  theorems is what ultimately justifies using [r] (as produced by
  whatever external analysis constructs it) to inform real program
  transformations: [check_const_program p r = true] plus
  [VarMap.find v pp_info = Some c] at a reachable program point implies
  the value of [v] there is actually, always, [c]. *)
  Theorem check_const_program_snd :
    forall (p: CFGProgD.t) (r: ConstD.prog_const_info_t),
      ConstD.check_const_program p r = true ->
      forall (fn: FuncName.t) (f: CFGFunD.t) (f_info: ConstD.func_const_info_t)
             (bid: BlockID.t) (b: BlockD.t) (b_info: ConstD.block_const_info_t)
             (pc: nat) (pp_info: ConstD.pp_const_info_t) (v: VarID.t) (c: D.value_t),
        CFGProgD.get_func p fn = Some f ->
        r fn = Some f_info ->
        CFGProgD.get_block p fn bid = Some b ->
        f_info bid = Some b_info ->
        List.nth_error b_info pc = Some pp_info ->
        VarMap.find v pp_info = Some c ->
        ConstSndD.const_at_pc p fn bid pc v c.
  Proof.
    intros p r Hcheck fn f f_info bid b b_info pc pp_info v c
           Hgetf Hrf Hgetb Hfb Hnth Hfind.
    destruct (check_const_program_block_snd p r Hcheck fn bid f b Hgetf Hgetb)
      as [f_info' [b_info' [Hrf' [Hfb' [Hpp [Hedges Hentry_chk]]]]]].
    assert (Heq_f_info : f_info' = f_info)
      by (rewrite Hrf in Hrf'; injection Hrf' as Hrf'; exact (eq_sym Hrf')).
    subst f_info'.
    assert (Heq_b_info : b_info' = b_info)
      by (rewrite Hfb in Hfb'; injection Hfb' as Hfb'; exact (eq_sym Hfb')).
    subst b_info'.
    exact (build_pp_info_snd_pc p r Hcheck fn bid f b f_info b_info
             Hgetf Hgetb Hrf Hfb Hpp Hedges Hentry_chk pc pp_info Hnth v c Hfind).
  Qed.

End Constancy_checker_snd.
