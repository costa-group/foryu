Require Import FORYU.state.
Require Import FORYU.program.
Require Import FORYU.semantics.
Require Import FORYU.constancy_info.
Require Import FORYU.constancy.
Require Import FORYU.constancy_snd.
Require Import FORYU.list_functions.

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import FSets.FMapFacts.

Module Constancy_checker_snd (D: DIALECT).

  (* [ConstSndD] is projected out of [ConstD], so that the checker and
  the specification share one [CFGProgD]/etc. lineage (see
  constancy_info.v). *)
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


  (* This file shows that the boolean checker [ConstD.check_const_program]
  only accepts valid constancy information, in the sense of
  [ConstSndD.const_in]/[const_out]/[const_at_pc] (constancy_snd.v) --
  the counterpart of liveness_snd.v's [check_program_correct]. *)

  (* ** [VarMap]/[update_const_info]/[derive_pairs] plumbing **

  [update_const_info m vs pairs] first [VarMap.remove]s every variable
  in [vs] from [m], then [VarMap.add]s every pair in [pairs]. The
  lemmas below pin down exactly what [VarMap.find] returns afterwards. *)

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
  two shapes needed below: with an empty [pairs]
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

  (* [ConstSndD.phi_source]'s own [List.find]/[List.combine] structure,
  characterized directly by index -- the two directions
  [sym_exec_phi_const_phi] needs, mirroring
  [derive_pairs_nth_error_some]/[derive_pairs_notin_vs_notin_fst], but
  for [phi_source]'s "first match" lookup instead of
  [derive_pairs]'s filtered zip. [NoDup vars] is exactly what pins the
  index found down to *the* (unique) occurrence. *)
  (* Stated over [PhiInfoD.SimpleExprD.t] -- the element type
  [phi_source] itself uses -- rather than the convertible, but not
  syntactically equal, [SimpleExprD.t], so that they can be used with
  [rewrite] after unfolding [phi_source]. *)
  Lemma phi_source_from_index :
    forall (vars: list VarID.t) (exprs: list PhiInfoD.SimpleExprD.t) (v: VarID.t) (k: nat) (e: PhiInfoD.SimpleExprD.t),
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
    forall (vars: list VarID.t) (exprs: list PhiInfoD.SimpleExprD.t) (v: VarID.t),
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

  Lemma in_InA_eq_key_elt :
    forall (l: list (VarID.t * D.value_t)) (v: VarID.t) (c: D.value_t),
      In (v, c) l -> SetoidList.InA (VarMap.eq_key_elt (elt:=D.value_t)) (v, c) l.
  Proof.
    induction l as [| [v0 c0] l' IH]; intros v c Hin.
    - destruct Hin.
    - destruct Hin as [Heq | Hin].
      + injection Heq as Heq1 Heq2. subst v0 c0.
        apply SetoidList.InA_cons_hd. split; reflexivity.
      + apply SetoidList.InA_cons_tl. exact (IH v c Hin).
  Qed.

  Lemma const_info_subset_complete :
    forall (m1 m2: ConstD.pp_const_info_t),
      (forall (v: VarID.t) (c: D.value_t), VarMap.find v m1 = Some c -> VarMap.find v m2 = Some c) ->
      ConstD.const_info_subset m1 m2 = true.
  Proof.
    intros m1 m2 Hent.
    unfold ConstD.const_info_subset.
    rewrite List.forallb_forall.
    intros [v c] Hin.
    simpl.
    assert (Hfind1 : VarMap.find v m1 = Some c)
      by exact (VarMap.find_1 (VarMap.elements_2 (in_InA_eq_key_elt (VarMap.elements m1) v c Hin))).
    rewrite (Hent v c Hfind1).
    apply DialectFactsD.eqb_refl.
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
  walk over [instrs]/[b_info] relates their positions. *)

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
  needed by [ConstD.check_const_edges]). *)
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

  (* ** The checker's symbolic execution satisfies the relational
  specification **

  [ConstD.sym_exec_instr]/[ConstD.sym_exec_phi] compute information
  that is valid in the sense of [ConstSndD.const_at_pc_instr]/
  [ConstSndD.const_phi]; and so is anything included in it, which is
  what [ConstD.check_const_instr]/[ConstD.check_const_successor]
  check. *)

  (* [instr_snd i m m']: the last premise of
  [ConstSndD.const_at_pc_instr], i.e., every fact claimed by [m'] right
  after instruction [i] is justified by [m] right before it. Named here
  only to state the lemmas below. *)
  Definition instr_snd (i: InstrD.t) (m m': ConstD.pp_const_info_t) : Prop :=
    forall (v: VarID.t) (c: D.value_t),
      VarMap.find v m' = Some c ->
      (~ In v i.(output) /\ VarMap.find v m = Some c)
      \/ (i.(InstrD.op) = inr ASSIGN /\
          exists (k: nat) (x: SimpleExprD.t),
            nth_error i.(output) k = Some v /\
            nth_error i.(input) k = Some x /\
            ConstSndD.sexpr_const m x c)
      \/ (exists (opcode: D.opcode_t) (k: nat) (cs res_vals: list D.value_t) (st: D.dialect_state_t),
            i.(InstrD.op) = inl (inr opcode) /\
            D.opcode_indep_state opcode = true /\
            Forall2 (ConstSndD.sexpr_const m) i.(input) cs /\
            D.execute_opcode D.empty_dialect_state opcode cs = (res_vals, st, Status.Running) /\
            nth_error i.(output) k = Some v /\
            nth_error res_vals k = Some c).

  Lemma eval_sexpr_pp_sexpr_const :
    forall (m: ConstD.pp_const_info_t) (x: SimpleExprD.t) (c: D.value_t),
      ConstD.eval_sexpr_pp m x = Some c -> ConstSndD.sexpr_const m x c.
  Proof.
    intros m x c H.
    destruct x as [v | val]; simpl in *.
    - exact H.
    - injection H as H. exact (eq_sym H).
  Qed.

  Lemma option_list_eval_sexpr_pp_forall2 :
    forall (m: ConstD.pp_const_info_t) (es: list SimpleExprD.t) (cs: list D.value_t),
      ListFunctions.option_list (List.map (ConstD.eval_sexpr_pp m) es) = Some cs ->
      Forall2 (ConstSndD.sexpr_const m) es cs.
  Proof.
    intros m es.
    induction es as [| x es' IH]; intros cs Hlist.
    - simpl in Hlist. injection Hlist as Hlist. subst cs. constructor.
    - simpl in Hlist.
      destruct (ConstD.eval_sexpr_pp m x) as [c|] eqn:Heval; try discriminate.
      destruct (ListFunctions.option_list (List.map (ConstD.eval_sexpr_pp m) es')) as [cs'|] eqn:Hlist'; try discriminate.
      injection Hlist as Hlist. subst cs.
      constructor.
      + exact (eval_sexpr_pp_sexpr_const m x c Heval).
      + exact (IH cs' eq_refl).
  Qed.

  Lemma sym_exec_instr_snd :
    forall (i: InstrD.t) (m: ConstD.pp_const_info_t),
      instr_snd i m (ConstD.sym_exec_instr i m).
  Proof.
    intros i m v c Hfind.
    destruct (List.in_dec VarMapFacts.eq_dec v i.(output)) as [Hin | Hnotin].
    - right.
      unfold ConstD.sym_exec_instr in Hfind.
      destruct (i.(InstrD.op)) as [[callee | opcode] | aux] eqn:Hop.
      + exfalso. rewrite (update_const_info_empty_in m i.(output) v Hin) in Hfind. discriminate Hfind.
      + destruct (ListFunctions.option_list (List.map (ConstD.eval_sexpr_pp m) i.(input))) as [cs|] eqn:Hoptlist.
        * destruct (D.opcode_indep_state opcode) eqn:Hindep.
          -- destruct (D.execute_opcode D.empty_dialect_state opcode cs) as [[res_vals st] status] eqn:Hexec.
             destruct status as [ | | | msg] eqn:Hstatus;
               try (exfalso; rewrite (update_const_info_empty_in m i.(output) v Hin) in Hfind; discriminate Hfind).
             destruct (List.in_dec VarMapFacts.eq_dec v (List.map fst (ConstD.derive_pairs i.(output) (List.map (fun v0 => Some v0) res_vals)))) as [HinPairs | HnotinPairs].
             ++ apply List.in_map_iff in HinPairs. destruct HinPairs as [[v' val'] [Heqfst HinPairs']].
                simpl in Heqfst. subst v'.
                rewrite (update_const_info_in_pairs m i.(output) _ v val' HinPairs'
                           (derive_pairs_nodup i.(output) _ i.(InstrD.H_nodup))) in Hfind.
                injection Hfind as Hfind. subst val'.
                destruct (derive_pairs_in_iff_nth_error i.(output) (List.map (fun v0 => Some v0) res_vals) v c HinPairs') as [k [Hk1 Hk2]].
                right. exists opcode, k, cs, res_vals, st.
                repeat split;
                  first [ reflexivity
                        | exact Hindep
                        | exact Hexec
                        | exact (option_list_eval_sexpr_pp_forall2 m i.(input) cs Hoptlist)
                        | exact Hk1
                        | exact (map_some_nth_error_some res_vals k c Hk2) ].
             ++ exfalso.
                rewrite (update_const_info_notin_pairs_in_vs m i.(output) _ v HnotinPairs Hin) in Hfind.
                discriminate Hfind.
          -- exfalso. rewrite (update_const_info_empty_in m i.(output) v Hin) in Hfind. discriminate Hfind.
        * exfalso. rewrite (update_const_info_empty_in m i.(output) v Hin) in Hfind. discriminate Hfind.
      + destruct aux.
        destruct (List.in_dec VarMapFacts.eq_dec v (List.map fst (ConstD.derive_pairs i.(output) (List.map (ConstD.eval_sexpr_pp m) i.(input))))) as [HinPairs | HnotinPairs].
        * apply List.in_map_iff in HinPairs. destruct HinPairs as [[v' val'] [Heqfst HinPairs']].
          simpl in Heqfst. subst v'.
          rewrite (update_const_info_in_pairs m i.(output) _ v val' HinPairs'
                     (derive_pairs_nodup i.(output) _ i.(InstrD.H_nodup))) in Hfind.
          injection Hfind as Hfind. subst val'.
          destruct (derive_pairs_in_iff_nth_error i.(output) (List.map (ConstD.eval_sexpr_pp m) i.(input)) v c HinPairs') as [k [Hk1 Hk2]].
          destruct (eval_sexpr_pp_nth_error_some m i.(input) k c Hk2) as [x [Hxeq Hevalx]].
          left. split; [reflexivity | ].
          exists k, x. repeat split; [exact Hk1 | exact Hxeq | exact (eval_sexpr_pp_sexpr_const m x c Hevalx)].
        * exfalso.
          rewrite (update_const_info_notin_pairs_in_vs m i.(output) _ v HnotinPairs Hin) in Hfind.
          discriminate Hfind.
    - left. split; [exact Hnotin | ].
      rewrite (sym_exec_instr_unaffected m i v Hnotin) in Hfind.
      exact Hfind.
  Qed.

  Lemma instr_snd_incl :
    forall (i: InstrD.t) (m m1 m2: ConstD.pp_const_info_t),
      instr_snd i m m2 ->
      (forall (v: VarID.t) (c: D.value_t), VarMap.find v m1 = Some c -> VarMap.find v m2 = Some c) ->
      instr_snd i m m1.
  Proof.
    intros i m m1 m2 H Hincl v c Hfind. exact (H v c (Hincl v c Hfind)).
  Qed.

  Lemma check_const_instr_snd :
    forall (i: InstrD.t) (Cb Ca: ConstD.pp_const_info_t),
      ConstD.check_const_instr i Cb Ca = true -> instr_snd i Cb Ca.
  Proof.
    intros i Cb Ca Hcheck.
    exact (instr_snd_incl i Cb Ca _ (sym_exec_instr_snd i Cb)
             (const_info_subset_spec Ca _ Hcheck)).
  Qed.

  Lemma sym_exec_phi_const_phi :
    forall (b: BlockD.t) (pred_bid: BlockID.t) (m_pred: ConstD.pp_const_info_t),
      ConstSndD.const_phi b pred_bid m_pred (ConstD.sym_exec_phi b pred_bid m_pred).
  Proof.
    intros b pred_bid m_pred v c Hfind.
    unfold ConstD.sym_exec_phi in Hfind.
    destruct (snd b.(phi_function) pred_bid) as [in_sexprs] eqn:Hphi.
    unfold ConstSndD.phi_source.
    rewrite Hphi.
    assert (Hfind' : VarMap.find v (ConstD.update_const_info m_pred (fst b.(phi_function))
                         (ConstD.derive_pairs (fst b.(phi_function)) (List.map (ConstD.eval_sexpr_pp m_pred) in_sexprs))) = Some c)
      by exact Hfind.
    destruct (List.in_dec VarMapFacts.eq_dec v (fst b.(phi_function))) as [Hin | Hnotin].
    - destruct (List.in_dec VarMapFacts.eq_dec v (List.map fst (ConstD.derive_pairs (fst b.(phi_function)) (List.map (ConstD.eval_sexpr_pp m_pred) in_sexprs)))) as [HinPairs | HnotinPairs].
      + apply List.in_map_iff in HinPairs. destruct HinPairs as [[v' val'] [Heqfst HinPairs']].
        simpl in Heqfst. subst v'.
        rewrite (update_const_info_in_pairs m_pred (fst b.(phi_function)) _ v val' HinPairs'
                   (derive_pairs_nodup (fst b.(phi_function)) _ b.(BlockD.H_phi_nodup))) in Hfind'.
        injection Hfind' as Hfind'. subst val'.
        destruct (derive_pairs_in_iff_nth_error (fst b.(phi_function)) (List.map (ConstD.eval_sexpr_pp m_pred) in_sexprs) v c HinPairs') as [k [Hk1 Hk2]].
        destruct (eval_sexpr_pp_nth_error_some m_pred in_sexprs k c Hk2) as [x [Hxeq Hevalx]].
        rewrite (phi_source_from_index (fst b.(phi_function)) in_sexprs v k x b.(BlockD.H_phi_nodup) Hk1 Hxeq).
        right. exists x. split; [reflexivity | exact (eval_sexpr_pp_sexpr_const m_pred x c Hevalx)].
      + exfalso.
        rewrite (update_const_info_notin_pairs_in_vs m_pred (fst b.(phi_function)) _ v HnotinPairs Hin) in Hfind'.
        discriminate Hfind'.
    - assert (Heq2 : VarMap.find v (ConstD.update_const_info m_pred (fst b.(phi_function))
                         (ConstD.derive_pairs (fst b.(phi_function)) (List.map (ConstD.eval_sexpr_pp m_pred) in_sexprs))) = VarMap.find v m_pred).
      { unfold ConstD.update_const_info.
        rewrite (fold_left_add_notin _ _ v (derive_pairs_notin_vs_notin_fst (fst b.(phi_function)) _ v Hnotin)).
        exact (fold_left_remove_notin (fst b.(phi_function)) m_pred v Hnotin). }
      rewrite Heq2 in Hfind'.
      left. split; [exact Hnotin | exact Hfind'].
  Qed.

  (* ** Wiring the whole-program checker down to a specific block **

  [CFGProgD.get_func]/[CFGFunD.get_block] both resolve via a [FuncNameMap]/
  [BlockMap] index built from [functions]/[blocks] (see program.v), so a
  successful lookup's own result is (a) a member of the list indexed, and
  (b) matches the query on the field being compared -- exactly what
  [get_func_sound]/[get_block_sound] give directly. *)
  Lemma get_func_in :
    forall (p: CFGProgD.t) (fn: FuncName.t) (f: CFGFunD.t),
      CFGProgD.get_func p fn = Some f -> In f p.(functions).
  Proof.
    intros p fn f Hget.
    exact (proj1 (CFGProgD.get_func_sound p fn f Hget)).
  Qed.

  Lemma get_func_name_eq :
    forall (p: CFGProgD.t) (fn: FuncName.t) (f: CFGFunD.t),
      CFGProgD.get_func p fn = Some f -> f.(CFGFunD.name) = fn.
  Proof.
    intros p fn f Hget.
    exact (proj2 (CFGProgD.get_func_sound p fn f Hget)).
  Qed.

  Lemma get_block_in :
    forall (p: CFGProgD.t) (fn: FuncName.t) (bid: BlockID.t) (f: CFGFunD.t) (b: BlockD.t),
      CFGProgD.get_func p fn = Some f ->
      CFGProgD.get_block p fn bid = Some b -> In b f.(blocks).
  Proof.
    intros p fn bid f b Hgetf Hgetb.
    unfold CFGProgD.get_block in Hgetb.
    rewrite Hgetf in Hgetb.
    exact (proj1 (CFGFunD.get_block_sound f bid b Hgetb)).
  Qed.

  Lemma get_block_bid_eq :
    forall (p: CFGProgD.t) (fn: FuncName.t) (bid: BlockID.t) (f: CFGFunD.t) (b: BlockD.t),
      CFGProgD.get_func p fn = Some f ->
      CFGProgD.get_block p fn bid = Some b -> b.(BlockD.bid) = bid.
  Proof.
    intros p fn bid f b Hgetf Hgetb.
    unfold CFGProgD.get_block in Hgetb.
    rewrite Hgetf in Hgetb.
    exact (proj2 (CFGFunD.get_block_sound f bid b Hgetb)).
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

  Lemma block_entry_info_of_nth0 :
    forall (b_info: ConstD.block_const_info_t) (C: ConstD.pp_const_info_t),
      nth_error b_info 0 = Some C -> ConstD.block_entry_info b_info = Some C.
  Proof.
    intros b_info C H. destruct b_info as [| C0 rest]; [discriminate | exact H].
  Qed.

  Lemma nth0_of_block_entry_info :
    forall (b_info: ConstD.block_const_info_t) (C: ConstD.pp_const_info_t),
      ConstD.block_entry_info b_info = Some C -> nth_error b_info 0 = Some C.
  Proof.
    intros b_info C H. destruct b_info as [| C0 rest]; [discriminate | exact H].
  Qed.

  (* A block info with [S n] entries has an exit info, at position [n]. *)
  Lemma block_exit_info_nth :
    forall (b_info: ConstD.block_const_info_t) (n: nat),
      length b_info = S n ->
      exists (C: ConstD.pp_const_info_t),
        nth_error b_info n = Some C /\ ConstD.block_exit_info b_info = Some C.
  Proof.
    intros b_info n Hlen.
    destruct (List.exists_last (l := b_info)) as [l' [C Heq]].
    { intro Hnil. subst b_info. discriminate Hlen. }
    subst b_info.
    rewrite List.length_app in Hlen. simpl in Hlen.
    exists C. split.
    - rewrite List.nth_error_app2 by lia.
      replace (n - length l') with 0 by lia. reflexivity.
    - unfold ConstD.block_exit_info. rewrite List.rev_app_distr. reflexivity.
  Qed.

  (* ** Completeness of the checker's symbolic execution **

  Everything the relational specification justifies is also computed
  by [ConstD.sym_exec_instr]/[ConstD.sym_exec_phi] -- the converse of
  [sym_exec_instr_snd]/[sym_exec_phi_const_phi] above. *)

  Lemma sexpr_const_eval_sexpr_pp :
    forall (m: ConstD.pp_const_info_t) (x: SimpleExprD.t) (c: D.value_t),
      ConstSndD.sexpr_const m x c -> ConstD.eval_sexpr_pp m x = Some c.
  Proof.
    intros m x c H.
    destruct x as [v | val]; simpl in *.
    - exact H.
    - subst c. reflexivity.
  Qed.

  Lemma forall2_option_list_eval_sexpr_pp :
    forall (m: ConstD.pp_const_info_t) (es: list SimpleExprD.t) (cs: list D.value_t),
      Forall2 (ConstSndD.sexpr_const m) es cs ->
      ListFunctions.option_list (List.map (ConstD.eval_sexpr_pp m) es) = Some cs.
  Proof.
    intros m es cs H.
    induction H as [| x c es' cs' Hx Hrest IH].
    - reflexivity.
    - simpl. rewrite (sexpr_const_eval_sexpr_pp m x c Hx), IH. reflexivity.
  Qed.

  Lemma eval_sexpr_pp_nth_error_intro :
    forall (m: ConstD.pp_const_info_t) (l: list SimpleExprD.t) (k: nat) (x: SimpleExprD.t) (c: D.value_t),
      nth_error l k = Some x ->
      ConstD.eval_sexpr_pp m x = Some c ->
      nth_error (List.map (ConstD.eval_sexpr_pp m) l) k = Some (Some c).
  Proof.
    induction l as [| x0 l' IH]; intros k x c Hnth Heval.
    - destruct k; discriminate.
    - destruct k as [| k'].
      + simpl in Hnth. injection Hnth as Hnth. subst x0. simpl. rewrite Heval. reflexivity.
      + simpl in Hnth |- *. exact (IH k' x c Hnth Heval).
  Qed.

  Lemma map_some_nth_error_intro :
    forall (l: list D.value_t) (k: nat) (c: D.value_t),
      nth_error l k = Some c ->
      nth_error (List.map (fun v0 => Some v0) l) k = Some (Some c).
  Proof.
    induction l as [| x0 l' IH]; intros k c Hnth.
    - destruct k; discriminate.
    - destruct k as [| k'].
      + simpl in Hnth |- *. injection Hnth as Hnth. subst x0. reflexivity.
      + simpl in Hnth |- *. exact (IH k' c Hnth).
  Qed.

  Lemma in_combine_nth_error :
    forall (A B: Type) (l1: list A) (l2: list B) (a: A) (b: B),
      In (a, b) (List.combine l1 l2) ->
      exists k, nth_error l1 k = Some a /\ nth_error l2 k = Some b.
  Proof.
    induction l1 as [| a0 l1' IH]; intros l2 a b Hin.
    - destruct Hin.
    - destruct l2 as [| b0 l2']; [destruct Hin | ].
      simpl in Hin. destruct Hin as [Heq | Hin].
      + injection Heq as Ha Hb. subst a0 b0. exists 0. split; reflexivity.
      + destruct (IH l2' a b Hin) as [k [H1 H2]]. exists (S k). split; [exact H1 | exact H2].
  Qed.

  Lemma sym_exec_instr_complete :
    forall (i: InstrD.t) (m m': ConstD.pp_const_info_t),
      instr_snd i m m' ->
      forall (v: VarID.t) (c: D.value_t),
        VarMap.find v m' = Some c -> VarMap.find v (ConstD.sym_exec_instr i m) = Some c.
  Proof.
    intros i m m' H v c Hfind.
    destruct (H v c Hfind) as
      [ [Hnotin Hfind_m]
      | [ [Hop [k [x [Hk [Hx Hxc]]]]]
        | [opcode [k [cs [res_vals [st [Hop [Hindep [Hcs [Hexec [Hk Hres]]]]]]]]]] ] ].
    - rewrite (sym_exec_instr_unaffected m i v Hnotin). exact Hfind_m.
    - unfold ConstD.sym_exec_instr. rewrite Hop.
      apply (update_const_info_in_pairs m i.(output) _ v c).
      + apply (derive_pairs_nth_error_some i.(output) _ k v c Hk).
        exact (eval_sexpr_pp_nth_error_intro m i.(input) k x c Hx (sexpr_const_eval_sexpr_pp m x c Hxc)).
      + exact (derive_pairs_nodup i.(output) _ i.(InstrD.H_nodup)).
    - unfold ConstD.sym_exec_instr. rewrite Hop.
      rewrite (forall2_option_list_eval_sexpr_pp m i.(input) cs Hcs), Hindep, Hexec.
      apply (update_const_info_in_pairs m i.(output) _ v c).
      + exact (derive_pairs_nth_error_some i.(output) _ k v c Hk (map_some_nth_error_intro res_vals k c Hres)).
      + exact (derive_pairs_nodup i.(output) _ i.(InstrD.H_nodup)).
  Qed.

  Lemma sym_exec_phi_complete :
    forall (b: BlockD.t) (pred_bid: BlockID.t) (m_pred m: ConstD.pp_const_info_t),
      ConstSndD.const_phi b pred_bid m_pred m ->
      forall (v: VarID.t) (c: D.value_t),
        VarMap.find v m = Some c -> VarMap.find v (ConstD.sym_exec_phi b pred_bid m_pred) = Some c.
  Proof.
    intros b pred_bid m_pred m H v c Hfind.
    unfold ConstD.sym_exec_phi.
    destruct (snd b.(phi_function) pred_bid) as [in_sexprs] eqn:Hphi.
    change (VarMap.find v (ConstD.update_const_info m_pred (fst b.(phi_function))
              (ConstD.derive_pairs (fst b.(phi_function)) (List.map (ConstD.eval_sexpr_pp m_pred) in_sexprs))) = Some c).
    destruct (H v c Hfind) as [[Hnotin Hfind_pred] | [x [Hsome Hxc]]].
    - unfold ConstD.update_const_info.
      rewrite (fold_left_add_notin _ _ v (derive_pairs_notin_vs_notin_fst (fst b.(phi_function)) _ v Hnotin)).
      rewrite (fold_left_remove_notin (fst b.(phi_function)) m_pred v Hnotin).
      exact Hfind_pred.
    - unfold ConstSndD.phi_source in Hsome. rewrite Hphi in Hsome. cbv beta iota zeta in Hsome.
      destruct (List.find (fun ov => VarID.eqb (fst ov) v) (List.combine (fst b.(phi_function)) in_sexprs))
        as [[v'' e]|] eqn:Hfind_phi; [ | discriminate Hsome].
      injection Hsome as Hsome. subst e.
      destruct (List.find_some _ _ Hfind_phi) as [Hin Hv''].
      simpl in Hv''. apply VarID.eqb_eq in Hv''. subst v''.
      destruct (in_combine_nth_error _ _ _ _ v x Hin) as [k [Hk1 Hk2]].
      apply (update_const_info_in_pairs m_pred (fst b.(phi_function)) _ v c).
      + apply (derive_pairs_nth_error_some (fst b.(phi_function)) _ k v c Hk1).
        exact (eval_sexpr_pp_nth_error_intro m_pred in_sexprs k x c Hk2 (sexpr_const_eval_sexpr_pp m_pred x c Hxc)).
      + exact (derive_pairs_nodup (fst b.(phi_function)) _ b.(BlockD.H_phi_nodup)).
  Qed.

  (* ** Valid analysis results **

  [const_info_snd p r] states that the analysis result [r] is valid
  for [p], block by block, in terms of the specification in
  constancy_snd.v -- the counterpart of liveness's
  [snd_all_blocks_info]. For every block of every function, [r] has
  one map per program point of the block (one more than its number of
  instructions), such that:

  - the entry map of the function's entry block is empty;
  - the map after each instruction is justified by the map before it
    (the last premise of [ConstSndD.const_at_pc_instr]);
  - the entry map of every successor is justified, through its
    phi-function, by the block's exit map ([ConstSndD.const_phi]). *)

  (* The edge from block [pred_bid] (with exit map [m_exit]) to its
  successor [next_bid]. *)
  Definition edge_info_snd (p: CFGProgD.t) (f_info: ConstD.func_const_info_t) (fname: FuncName.t)
    (pred_bid: BlockID.t) (m_exit: ConstD.pp_const_info_t) (next_bid: BlockID.t) : Prop :=
    exists (next_b: BlockD.t) (next_b_info: ConstD.block_const_info_t) (next_entry: ConstD.pp_const_info_t),
      CFGProgD.get_block p fname next_bid = Some next_b /\
      f_info next_bid = Some next_b_info /\
      nth_error next_b_info 0 = Some next_entry /\
      ConstSndD.const_phi next_b pred_bid m_exit next_entry.

  Definition block_info_snd (p: CFGProgD.t) (r: ConstD.prog_const_info_t) (fname: FuncName.t)
    (f: CFGFunD.t) (bid: BlockID.t) (b: BlockD.t) : Prop :=
    exists (f_info: ConstD.func_const_info_t) (b_info: ConstD.block_const_info_t),
      r fname = Some f_info /\ (* the information of the function exists *)
      f_info bid = Some b_info /\ (* the information of the block exists *)
      length b_info = S (length b.(instructions)) /\ (* one map per program point *)
      (* nothing is known at the entry of the function *)
      (bid = f.(entry_bid) -> forall (m: ConstD.pp_const_info_t), nth_error b_info 0 = Some m -> VarMap.Empty m) /\
      (* each instruction *)
      (forall (pc: nat) (i: InstrD.t) (m m': ConstD.pp_const_info_t),
          nth_error b.(instructions) pc = Some i ->
          nth_error b_info pc = Some m ->
          nth_error b_info (S pc) = Some m' ->
          instr_snd i m m') /\
      (* each outgoing edge *)
      (forall (m_exit: ConstD.pp_const_info_t),
          nth_error b_info (length b.(instructions)) = Some m_exit ->
          match b.(exit_info) with
          | ExitInfoD.Jump next_bid =>
              edge_info_snd p f_info fname bid m_exit next_bid
          | ExitInfoD.ConditionalJump _ next_bid_if_true next_bid_if_false =>
              edge_info_snd p f_info fname bid m_exit next_bid_if_true /\
              edge_info_snd p f_info fname bid m_exit next_bid_if_false
          | _ => True
          end).

  Definition const_info_snd (p: CFGProgD.t) (r: ConstD.prog_const_info_t) : Prop :=
    forall (fname: FuncName.t) (f: CFGFunD.t) (bid: BlockID.t) (b: BlockD.t),
      CFGProgD.get_func p fname = Some f ->
      CFGProgD.get_block p fname bid = Some b -> (* if the block exists *)
      block_info_snd p r fname f bid b. (* it has valid information *)

  (* ** The checker accepts only valid results ** *)

  Lemma check_const_successor_edge :
    forall (p: CFGProgD.t) (f_info: ConstD.func_const_info_t) (fname: FuncName.t) (pred_bid: BlockID.t) (m_exit: ConstD.pp_const_info_t) (next_bid: BlockID.t),
      ConstD.check_const_successor p f_info fname pred_bid m_exit next_bid = true ->
      edge_info_snd p f_info fname pred_bid m_exit next_bid.
  Proof.
    intros p f_info fname pred_bid m_exit next_bid Hcheck.
    unfold ConstD.check_const_successor in Hcheck.
    destruct (CFGProgD.get_block p fname next_bid) as [next_b|] eqn:Hnb; [ | discriminate].
    destruct (f_info next_bid) as [next_b_info|] eqn:Hnbi; [ | discriminate].
    destruct (ConstD.block_entry_info next_b_info) as [next_entry|] eqn:Hne; [ | discriminate].
    exists next_b, next_b_info, next_entry.
    split; [exact Hnb | split; [exact Hnbi | split]].
    - exact (nth0_of_block_entry_info next_b_info next_entry Hne).
    - intros v c Hfind.
      exact (sym_exec_phi_const_phi next_b pred_bid m_exit v c (const_info_subset_spec next_entry _ Hcheck v c Hfind)).
  Qed.

  Lemma check_const_program_info_snd :
    forall (p: CFGProgD.t) (r: ConstD.prog_const_info_t),
      ConstD.check_const_program p r = true -> const_info_snd p r.
  Proof.
    intros p r Hcheck fname f bid b Hgetf Hgetb.
    destruct (check_const_program_block_snd p r Hcheck fname bid f b Hgetf Hgetb)
      as [f_info [b_info [Hrf [Hfb [Hpp [Hedges Hentry]]]]]].
    assert (Hbid_eq : b.(BlockD.bid) = bid) by exact (get_block_bid_eq p fname bid f b Hgetf Hgetb).
    destruct (check_const_pp_endpoints b.(instructions) b_info Hpp) as [C0 [Cend [H0 [Hend Hexit]]]].
    exists f_info, b_info.
    split; [exact Hrf | split; [exact Hfb | split; [exact (check_const_pp_length _ _ Hpp) | split; [ | split]]]].
    - (* entry *)
      intros Heq m Hm.
      unfold ConstD.check_const_entry in Hentry.
      rewrite Hbid_eq, Heq, (proj2 (BlockID.eqb_eq _ _) eq_refl) in Hentry.
      rewrite (block_entry_info_of_nth0 b_info m Hm) in Hentry.
      exact (VarMap.is_empty_2 Hentry).
    - (* instructions *)
      intros pc i m m' Hi Hm Hm'.
      destruct (check_const_pp_pointwise b.(instructions) b_info Hpp pc i Hi) as [Cb [Ca [HCb [HCa Hchk]]]].
      rewrite Hm in HCb. injection HCb as HCb. subst Cb.
      rewrite Hm' in HCa. injection HCa as HCa. subst Ca.
      exact (check_const_instr_snd i m m' Hchk).
    - (* edges *)
      intros m_exit Hm_exit.
      rewrite Hend in Hm_exit. injection Hm_exit as Hm_exit. subst m_exit.
      unfold ConstD.check_const_edges in Hedges.
      rewrite Hexit, Hbid_eq in Hedges.
      destruct (b.(exit_info)) as [cond_var nt nf | nj | rs | ].
      + apply andb_true_iff in Hedges. destruct Hedges as [Ht Hf].
        split; [exact (check_const_successor_edge _ _ _ _ _ _ Ht) | exact (check_const_successor_edge _ _ _ _ _ _ Hf)].
      + exact (check_const_successor_edge _ _ _ _ _ _ Hedges).
      + exact I.
      + exact I.
  Qed.

  (* ** The checker accepts all valid results ** *)

  Lemma check_const_pp_complete :
    forall (instrs: list InstrD.t) (b_info: ConstD.block_const_info_t),
      length b_info = S (length instrs) ->
      (forall (pc: nat) (i: InstrD.t) (m m': ConstD.pp_const_info_t),
          nth_error instrs pc = Some i -> nth_error b_info pc = Some m -> nth_error b_info (S pc) = Some m' ->
          instr_snd i m m') ->
      ConstD.check_const_pp instrs b_info = true.
  Proof.
    induction instrs as [| i instrs' IH]; intros b_info Hlen Hinstr; simpl.
    - destruct b_info as [| Cb0 [| Ca0 rest0]]; simpl in Hlen; try discriminate.
      reflexivity.
    - destruct b_info as [| Cb [| Ca rest]]; simpl in Hlen; try discriminate.
      assert (Hi : ConstD.check_const_instr i Cb Ca = true).
      { apply const_info_subset_complete.
        exact (sym_exec_instr_complete i Cb Ca (Hinstr 0 i Cb Ca eq_refl eq_refl eq_refl)). }
      rewrite Hi.
      apply IH.
      + simpl in Hlen |- *. lia.
      + intros pc i0 m m' Hi0 Hm Hm'. exact (Hinstr (S pc) i0 m m' Hi0 Hm Hm').
  Qed.

  Lemma edge_check_const_successor :
    forall (p: CFGProgD.t) (f_info: ConstD.func_const_info_t) (fname: FuncName.t) (pred_bid: BlockID.t) (m_exit: ConstD.pp_const_info_t) (next_bid: BlockID.t),
      edge_info_snd p f_info fname pred_bid m_exit next_bid ->
      ConstD.check_const_successor p f_info fname pred_bid m_exit next_bid = true.
  Proof.
    intros p f_info fname pred_bid m_exit next_bid [next_b [next_b_info [next_entry [Hnb [Hnbi [Hne Hphi]]]]]].
    unfold ConstD.check_const_successor.
    rewrite Hnb, Hnbi, (block_entry_info_of_nth0 next_b_info next_entry Hne).
    apply const_info_subset_complete.
    exact (sym_exec_phi_complete next_b pred_bid m_exit next_entry Hphi).
  Qed.

  Lemma check_const_blocks_complete :
    forall (bs: list BlockD.t) (f: CFGFunD.t) (p: CFGProgD.t) (r: ConstD.prog_const_info_t),
      (forall (b: BlockD.t), In b bs ->
         exists (f_info: ConstD.func_const_info_t) (b_info: ConstD.block_const_info_t),
           r f.(CFGFunD.name) = Some f_info /\ f_info b.(BlockD.bid) = Some b_info /\
           ConstD.check_const_pp b.(instructions) b_info = true /\
           ConstD.check_const_edges p f_info f.(CFGFunD.name) b b_info = true /\
           ConstD.check_const_entry f b b_info = true) ->
      ConstD.check_const_blocks bs f p r = true.
  Proof.
    induction bs as [| b0 bs' IH]; intros f p r Hbs.
    - reflexivity.
    - destruct (Hbs b0 (in_eq b0 bs')) as [f_info [b_info [Hrf [Hfb [Hpp [Hedges Hentry]]]]]].
      simpl. rewrite Hrf, Hfb, Hpp, Hedges, Hentry. simpl.
      apply IH. intros b Hin. exact (Hbs b (in_cons b0 b bs' Hin)).
  Qed.

  Lemma check_const_functions_complete :
    forall (fs: list CFGFunD.t) (p: CFGProgD.t) (r: ConstD.prog_const_info_t),
      (forall (f: CFGFunD.t), In f fs -> ConstD.check_const_blocks f.(blocks) f p r = true) ->
      ConstD.check_const_functions fs p r = true.
  Proof.
    induction fs as [| f0 fs' IH]; intros p r Hfs.
    - reflexivity.
    - simpl. rewrite (Hfs f0 (in_eq f0 fs')).
      apply IH. intros f Hin. exact (Hfs f (in_cons f0 f fs' Hin)).
  Qed.

  Lemma const_info_snd_check_const_program :
    forall (p: CFGProgD.t) (r: ConstD.prog_const_info_t),
      CFGProgD.valid_program p ->
      const_info_snd p r -> ConstD.check_const_program p r = true.
  Proof.
    intros p r Hvalid Hsnd.
    destruct Hvalid as [Hnames Hvalidf].
    unfold ConstD.check_const_program.
    apply check_const_functions_complete. intros f Hinf.
    apply check_const_blocks_complete. intros b Hinb.
    assert (Hgetf : CFGProgD.get_func p f.(CFGFunD.name) = Some f) by exact (proj1 (Hnames f) Hinf).
    assert (Hgetb : CFGProgD.get_block p f.(CFGFunD.name) b.(BlockD.bid) = Some b).
    { unfold CFGProgD.get_block. rewrite Hgetf. exact (proj1 (Hvalidf f Hinf b) Hinb). }
    destruct (Hsnd f.(CFGFunD.name) f b.(BlockD.bid) b Hgetf Hgetb)
      as [f_info [b_info [Hrf [Hfb [Hlen [Hentry [Hinstr Hedges]]]]]]].
    exists f_info, b_info.
    split; [exact Hrf | split; [exact Hfb | split; [ | split]]].
    - exact (check_const_pp_complete b.(instructions) b_info Hlen Hinstr).
    - destruct (block_exit_info_nth b_info (length b.(instructions)) Hlen) as [m_exit [Hnth Hexit]].
      specialize (Hedges m_exit Hnth).
      unfold ConstD.check_const_edges. rewrite Hexit.
      destruct (b.(exit_info)) as [cond_var nt nf | nj | rs | ].
      + destruct Hedges as [Ht Hf].
        rewrite (edge_check_const_successor _ _ _ _ _ _ Ht), (edge_check_const_successor _ _ _ _ _ _ Hf).
        reflexivity.
      + exact (edge_check_const_successor _ _ _ _ _ _ Hedges).
      + reflexivity.
      + reflexivity.
    - unfold ConstD.check_const_entry.
      destruct (BlockID.eqb b.(BlockD.bid) f.(entry_bid)) eqn:Heq; [ | reflexivity].
      apply BlockID.eqb_eq in Heq.
      destruct b_info as [| m0 rest]; [discriminate Hlen | ].
      apply VarMap.is_empty_1.
      exact (Hentry Heq m0 eq_refl).
  Qed.

  (* Soundness and completeness of the checker: a result is accepted
  exactly when it is valid -- the counterpart of liveness's
  [check_valid_prog_correct]. *)
  Theorem const_chk_snd_cmp :
    forall (p: CFGProgD.t) (r: ConstD.prog_const_info_t),
      CFGProgD.valid_program p ->
      (const_info_snd p r <-> ConstD.check_const_program p r = true).
  Proof.
    intros p r Hvalid. split.
    - exact (const_info_snd_check_const_program p r Hvalid).
    - exact (check_const_program_info_snd p r).
  Qed.

  (* ** Valid results satisfy the specification **

  [build_const_at_pc] shows that every map of a valid result [r] is
  valid in the sense of [ConstSndD.const_at_pc] -- productively, since
  the CFG may loop, exactly as [build_live_in]/[build_live_out] do for
  liveness. The within-block recursion (on [pc]) is part of the
  [CoFixpoint] itself rather than a separate lemma proven by
  induction: Coq's guardedness checker cannot see through such a
  lemma, and at [pc = 0] we need the corecursive call for the exit map
  of every predecessor (under [ConstSndD.const_out_block]). *)
  CoFixpoint build_const_at_pc
    (p: CFGProgD.t) (r: ConstD.prog_const_info_t) (Hsnd: const_info_snd p r)
    (fn: FuncName.t) (bid: BlockID.t) (f: CFGFunD.t) (b: BlockD.t)
    (f_info: ConstD.func_const_info_t) (b_info: ConstD.block_const_info_t)
    (Hgetf: CFGProgD.get_func p fn = Some f) (Hgetb: CFGProgD.get_block p fn bid = Some b)
    (Hrf: r fn = Some f_info) (Hfb: f_info bid = Some b_info)
    (pc: nat) (C: ConstD.pp_const_info_t) (HC: nth_error b_info pc = Some C)
    : ConstSndD.const_at_pc p fn bid pc C.
  Proof.
    destruct (Hsnd fn f bid b Hgetf Hgetb) as [f_info' [b_info' [Hrf' [Hfb' [Hlen [Hentry [Hinstr _]]]]]]].
    rewrite Hrf in Hrf'. injection Hrf' as Hrf'. subst f_info'.
    rewrite Hfb in Hfb'. injection Hfb' as Hfb'. subst b_info'.
    destruct pc as [| pc'].
    - (* pc = 0: the entry of the block *)
      apply ConstSndD.const_at_pc_entry.
      destruct (BlockID.eqb bid f.(entry_bid)) eqn:Hbideq.
      + (* the function's entry block: its entry map is empty *)
        apply BlockID.eqb_eq in Hbideq.
        exact (ConstSndD.const_in_entry p fn f bid C Hgetf Hbideq (Hentry Hbideq C HC)).
      + (* any other block: follows from every predecessor's exit map *)
        apply BlockID.eqb_neq_false in Hbideq.
        apply (ConstSndD.const_in_merge p fn f bid b C Hgetf Hbideq Hgetb).
        intros pred_bid pred_b Hispred.
        destruct Hispred as [Hpredblock Hexit_match].
        destruct (Hsnd fn f pred_bid pred_b Hgetf Hpredblock)
          as [pred_f_info [pred_b_info [Hpred_rf [Hpred_fb [Hpred_len [_ [_ Hpred_edges]]]]]]].
        rewrite Hrf in Hpred_rf. injection Hpred_rf as Hpred_rf. subst pred_f_info.
        destruct (block_exit_info_nth pred_b_info (length pred_b.(instructions)) Hpred_len) as [m_exit [Hm_exit _]].
        assert (Hedge : edge_info_snd p f_info fn pred_bid m_exit bid).
        { specialize (Hpred_edges m_exit Hm_exit).
          revert Hexit_match Hpred_edges.
          destruct (pred_b.(exit_info)) as [cond_var nt nf | nj | rs | ]; intros Hexit_match Hpred_edges.
          - destruct Hexit_match as [Heq | Heq]; subst.
            + exact (proj1 Hpred_edges).
            + exact (proj2 Hpred_edges).
          - subst nj. exact Hpred_edges.
          - destruct Hexit_match.
          - destruct Hexit_match. }
        destruct Hedge as [next_b [next_b_info [next_entry [Hnb [Hnbi [Hne Hphi]]]]]].
        rewrite Hgetb in Hnb. injection Hnb as Hnb. subst next_b.
        rewrite Hfb in Hnbi. injection Hnbi as Hnbi. subst next_b_info.
        rewrite HC in Hne. injection Hne as Hne. subst next_entry.
        exists m_exit. split.
        * exact (ConstSndD.const_out_block p fn pred_bid pred_b m_exit Hpredblock
                   (build_const_at_pc p r Hsnd fn pred_bid f pred_b f_info pred_b_info
                      Hgetf Hpredblock Hrf Hpred_fb (length pred_b.(instructions)) m_exit Hm_exit)).
        * exact Hphi.
    - (* pc = S pc': one more instruction *)
      assert (Hlt : S pc' < length b_info) by (apply List.nth_error_Some; rewrite HC; discriminate).
      destruct (nth_error b_info pc') as [Cb|] eqn:HCb;
        [ | exfalso; apply List.nth_error_None in HCb; lia].
      destruct (nth_error b.(instructions) pc') as [i|] eqn:Hi;
        [ | exfalso; apply List.nth_error_None in Hi; lia].
      exact (ConstSndD.const_at_pc_instr p fn bid b pc' i Cb C Hgetb Hi
               (build_const_at_pc p r Hsnd fn bid f b f_info b_info Hgetf Hgetb Hrf Hfb pc' Cb HCb)
               (Hinstr pc' i Cb C Hi HCb HC)).
  Qed.

  (* Every map of a valid result is valid in the sense of
  [ConstSndD.const_at_pc]. *)
  Theorem const_info_snd_const_at_pc :
    forall (p: CFGProgD.t) (r: ConstD.prog_const_info_t),
      const_info_snd p r ->
      forall (fn: FuncName.t) (f: CFGFunD.t) (f_info: ConstD.func_const_info_t)
             (bid: BlockID.t) (b: BlockD.t) (b_info: ConstD.block_const_info_t)
             (pc: nat) (m: ConstD.pp_const_info_t),
        CFGProgD.get_func p fn = Some f ->
        r fn = Some f_info ->
        CFGProgD.get_block p fn bid = Some b ->
        f_info bid = Some b_info ->
        List.nth_error b_info pc = Some m ->
        ConstSndD.const_at_pc p fn bid pc m.
  Proof.
    intros p r Hsnd fn f f_info bid b b_info pc m Hgetf Hrf Hgetb Hfb Hnth.
    exact (build_const_at_pc p r Hsnd fn bid f b f_info b_info Hgetf Hgetb Hrf Hfb pc m Hnth).
  Qed.

  (* Composing the above with [ConstSndD.const_at_pc_snd]: whatever a
  valid result claims at a program point really holds there, whenever
  execution reaches it. *)
  Corollary const_info_snd_constant_var :
    forall (p: CFGProgD.t) (r: ConstD.prog_const_info_t),
      const_info_snd p r ->
      forall (fn: FuncName.t) (f: CFGFunD.t) (f_info: ConstD.func_const_info_t)
             (bid: BlockID.t) (b: BlockD.t) (b_info: ConstD.block_const_info_t)
             (pc: nat) (m: ConstD.pp_const_info_t) (v: VarID.t) (c: D.value_t),
        CFGProgD.get_func p fn = Some f ->
        r fn = Some f_info ->
        CFGProgD.get_block p fn bid = Some b ->
        f_info bid = Some b_info ->
        List.nth_error b_info pc = Some m ->
        VarMap.find v m = Some c ->
        ConstSndD.constant_var p fn bid pc v c.
  Proof.
    intros p r Hsnd fn f f_info bid b b_info pc m v c Hgetf Hrf Hgetb Hfb Hnth Hfind.
    exact (ConstSndD.const_at_pc_snd p fn bid pc m
             (const_info_snd_const_at_pc p r Hsnd fn f f_info bid b b_info pc m Hgetf Hrf Hgetb Hfb Hnth)
             v c Hfind).
  Qed.

  (* The same, starting from the checker: [check_const_program p r =
  true] plus [VarMap.find v m = Some c] at a program point implies the
  value of [v] there is actually, always, [c]. *)
  Corollary check_const_program_constant_var :
    forall (p: CFGProgD.t) (r: ConstD.prog_const_info_t),
      ConstD.check_const_program p r = true ->
      forall (fn: FuncName.t) (f: CFGFunD.t) (f_info: ConstD.func_const_info_t)
             (bid: BlockID.t) (b: BlockD.t) (b_info: ConstD.block_const_info_t)
             (pc: nat) (m: ConstD.pp_const_info_t) (v: VarID.t) (c: D.value_t),
        CFGProgD.get_func p fn = Some f ->
        r fn = Some f_info ->
        CFGProgD.get_block p fn bid = Some b ->
        f_info bid = Some b_info ->
        List.nth_error b_info pc = Some m ->
        VarMap.find v m = Some c ->
        ConstSndD.constant_var p fn bid pc v c.
  Proof.
    intros p r Hcheck.
    exact (const_info_snd_constant_var p r (check_const_program_info_snd p r Hcheck)).
  Qed.

End Constancy_checker_snd.
