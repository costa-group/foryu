Require Import FORYU.dialect.
Require Import FORYU.program.
Require Import FORYU.list_functions.
Require Import FORYU.evm_dialect.
Require Import FORYU.constancy_info.

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Bool.

(* The abstract execution of EVM opcodes used by the constancy
analysis (an instance of [CONST_SYMB (EVMDialect BC)], for any
implementation [BC] of the blockchain operations, see
constancy_info.v). It has two parts:

  - if all inputs are known and the result of the opcode does not
    depend on the dialect state ([opcode_indep_state]), the opcode is
    executed (in the empty state);

  - otherwise, some opcodes give a known result even if some inputs
    are unknown ([abs_exec_partial]): [x - x] and [x * 0] are [0]. *)
Module EVMConstSymb (BC: BLOCK_CHAIN).

  (* the EVM dialect for this implementation of the blockchain
  operations (it shadows the functor [EVMDialect] in this module) *)
  Module EVMDialect := EVMDialect(BC).

  (* ** Opcodes whose result does not depend on the dialect state ** *)

  Definition opcode_indep_state (op: EVMDialect.opcode_t) := 
    match op with
    | EVM_opcode.ADD => true
    | EVM_opcode.SUB => true
    | EVM_opcode.MUL => true
    | EVM_opcode.DIV => true
    | EVM_opcode.SDIV => true
    | EVM_opcode.MOD => true
    | EVM_opcode.SMOD => true
    | EVM_opcode.EXP => true
    | EVM_opcode.NOT => true
    | EVM_opcode.LT => true
    | EVM_opcode.GT => true
    | EVM_opcode.SLT => true
    | EVM_opcode.SGT => true
    | EVM_opcode.EQ => true
    | EVM_opcode.ISZERO => true
    | EVM_opcode.AND => true
    | EVM_opcode.OR => true
    | EVM_opcode.XOR => true
    | EVM_opcode.BYTE => true
    | EVM_opcode.SHL => true
    | EVM_opcode.SHR => true
    | EVM_opcode.SAR => true
    | EVM_opcode.CLZ => true
    | EVM_opcode.ADDMOD => true
    | EVM_opcode.MULMOD => true
    | EVM_opcode.SIGNEXTEND => true
    | _ => false
    end.

  Ltac solve_binary_op op msg args :=
  simpl;
  destruct args as [|v [|v0 [|v1 args]]];
  (* We use [ | | | ] to explicitly handle the 4 cases created by the destruct above *)
  [ 
    (* Case: args = [] *)
    (exists []; exists (Status.Error msg); split; reflexivity) 
  | (* Case: args = [v] *)
    (exists []; exists (Status.Error msg); split; reflexivity)
  | (* Case: args = [v; v0] -> SUCCESS *)
    (exists [op v v0]; exists Status.Running; split; reflexivity)
  | (* Case: args = [v; v0; v1; ...] *)
    (exists []; exists (Status.Error msg); split; reflexivity)
  ].

  Ltac solve_unary_op op msg args :=
  simpl;
  destruct args as [|v [|v0 rest]];
  [ (* Case: [] *)
    (exists []; exists (Status.Error msg); split; reflexivity) 
  | (* Case: [v] -> SUCCESS *)
    (exists [op v]; exists Status.Running; split; reflexivity)
  | (* Case: [v; v0; ...] *)
    (exists []; exists (Status.Error msg); split; reflexivity)
  ].

  Ltac solve_ternary_op op msg args :=
  simpl;
  destruct args as [|v [|v0 [|v1 [|v2 rest]]]];
  [ (* Case: [] *)
    (exists []; exists (Status.Error msg); split; reflexivity) 
  | (* Case: [v] *)
    (exists []; exists (Status.Error msg); split; reflexivity)
  | (* Case: [v; v0] *)
    (exists []; exists (Status.Error msg); split; reflexivity)
  | (* Case: [v; v0; v1] -> SUCCESS *)
    (exists [op v v0 v1]; exists Status.Running; split; reflexivity)
  | (* Case: [v; v0; v1; v2; ...] *)
    (exists []; exists (Status.Error msg); split; reflexivity)
  ].

  Lemma opcode_indep_state_snd: forall (op: EVMDialect.opcode_t),
    opcode_indep_state op = true ->
    forall (s1 s2: EVMDialect.dialect_state_t) (args: list EVMDialect.value_t),
    exists (res: list EVMDialect.value_t) (status: Status.t),
    EVMDialect.execute_opcode s1 op args = (res, s1, status) /\
    EVMDialect.execute_opcode s2 op args = (res, s2, status).
  Proof.
    unfold EVMDialect.execute_opcode. intros op Hopcode s1 s2 args.
    destruct op; try (simpl in Hopcode; discriminate Hopcode).
    - solve_binary_op (U256.add) "ADD expects 2 inputs" args.
    - solve_binary_op (U256.sub) "SUB expects 2 inputs" args.
    - solve_binary_op (U256.mul) "MUL expects 2 inputs" args.
    - solve_binary_op (U256.div) "DIV expects 2 inputs" args.
    - solve_binary_op (U256.sdiv) "SDIV expects 2 inputs" args.
    - solve_binary_op (U256.mod_evm) "MOD expects 2 inputs" args.
    - solve_binary_op (U256.smod) "SMOD expects 2 inputs" args.
    - solve_binary_op (U256.exp) "EXP expects 2 inputs" args.
    - solve_unary_op (U256.not) "NOT expects 1 input" args.
    - solve_binary_op (U256.lt) "LT expects 2 inputs" args.
    - solve_binary_op (U256.gt) "GT expects 2 inputs" args.
    - solve_binary_op (U256.slt) "SLT expects 2 inputs" args.
    - solve_binary_op (U256.sgt) "SGT expects 2 inputs" args.
    - solve_binary_op (U256.eq) "EQ expects 2 inputs" args.
    - solve_unary_op (U256.iszero) "ISZERO expects 1 input" args.
    - solve_binary_op (U256.and) "AND expects 2 inputs" args.
    - solve_binary_op (U256.or) "OR expects 2 inputs" args.
    - solve_binary_op (U256.xor) "XOR expects 2 inputs" args.
    - solve_binary_op (U256.byte) "BYTE expects 2 inputs" args.
    - solve_binary_op (U256.shl) "SHL expects 2 inputs" args.
    - solve_binary_op (U256.shr) "SHR expects 2 inputs" args.
    - solve_binary_op (U256.sar) "SAR expects 2 inputs" args.
    - solve_unary_op (U256.clz) "CLZ expects 1 input" args.
    - solve_ternary_op (U256.addmod) "ADDMOD expects 3 inputs" args.
    - solve_ternary_op (U256.mulmod) "MULMOD expects 3 inputs" args. 
    - solve_binary_op (U256.signextend) "SIGNEXTEND expects 2 inputs" args.
  Qed.
      
  Definition empty_state : EVMDialect.dialect_state_t := EVMState.empty.

  (* ** Abstract execution ** *)

  (* The known value of an input, if any *)
  Definition known_value (known: VarID.t -> option EVMDialect.value_t) (e: VarID.t + EVMDialect.value_t)
    : option EVMDialect.value_t :=
    match e with
    | inl v => known v
    | inr c => Some c
    end.

  (* The input is known to be zero *)
  Definition known_zero (known: VarID.t -> option EVMDialect.value_t) (e: VarID.t + EVMDialect.value_t) : bool :=
    match known_value known e with
    | Some c => U256.eqb c U256.zero
    | None => false
    end.

  (* Opcodes with a known result even if some inputs are unknown *)
  Definition abs_exec_partial (op: EVMDialect.opcode_t) (es: list (VarID.t + EVMDialect.value_t))
    (known: VarID.t -> option EVMDialect.value_t) : option (list (option EVMDialect.value_t)) :=
    match op, es with
    | EVM_opcode.SUB, [inl x; inl y] => (* x - x = 0 *)
        if VarID.eqb x y then Some [Some U256.zero] else None
    | EVM_opcode.MUL, [e1; e2] => (* x * 0 = 0 * x = 0 *)
        if known_zero known e1 || known_zero known e2 then Some [Some U256.zero] else None
    | _, _ => None
    end.

  Definition abs_exec (op: EVMDialect.opcode_t) (es: list (VarID.t + EVMDialect.value_t))
    (known: VarID.t -> option EVMDialect.value_t) : option (list (option EVMDialect.value_t)) :=
    match ListFunctions.option_list (List.map (known_value known) es) with
    | Some cs =>
        if opcode_indep_state op then
          match EVMDialect.execute_opcode empty_state op cs with
          | (res, _, Status.Running) => Some (List.map Some res)
          | _ => abs_exec_partial op es known
          end
        else abs_exec_partial op es known
    | None => abs_exec_partial op es known
    end.

  (* ** Correctness ** *)

  Lemma known_value_eval :
    forall (known: VarID.t -> option EVMDialect.value_t) (rho: VarID.t -> EVMDialect.value_t)
           (e: VarID.t + EVMDialect.value_t) (c: EVMDialect.value_t),
      (forall (v: VarID.t) (c: EVMDialect.value_t), known v = Some c -> rho v = c) ->
      known_value known e = Some c ->
      (match e with inl v => rho v | inr c => c end) = c.
  Proof.
    intros known rho e c Hcons H.
    destruct e as [v | c']; simpl in *.
    - exact (Hcons v c H).
    - injection H as H. exact H.
  Qed.

  Lemma option_list_known_value :
    forall (known: VarID.t -> option EVMDialect.value_t) (rho: VarID.t -> EVMDialect.value_t)
           (es: list (VarID.t + EVMDialect.value_t)) (cs: list EVMDialect.value_t),
      (forall (v: VarID.t) (c: EVMDialect.value_t), known v = Some c -> rho v = c) ->
      ListFunctions.option_list (List.map (known_value known) es) = Some cs ->
      List.map (fun e => match e with inl v => rho v | inr c => c end) es = cs.
  Proof.
    intros known rho es.
    induction es as [| e es' IH]; intros cs Hcons H.
    - simpl in H. injection H as H. exact H.
    - simpl in H.
      destruct (known_value known e) as [c|] eqn:Hkv; [ | discriminate H].
      destruct (ListFunctions.option_list (List.map (known_value known) es')) as [cs'|] eqn:Hl; [ | discriminate H].
      injection H as H. subst cs.
      simpl. f_equal.
      + exact (known_value_eval known rho e c Hcons Hkv).
      + exact (IH cs' Hcons eq_refl).
  Qed.

  Lemma map_some_nth_error :
    forall (l: list EVMDialect.value_t) (k: nat) (c: EVMDialect.value_t),
      nth_error (List.map Some l) k = Some (Some c) -> nth_error l k = Some c.
  Proof.
    induction l as [| x l' IH]; intros k c H.
    - destruct k; discriminate H.
    - destruct k as [| k'].
      + simpl in H |- *. injection H as H. subst x. reflexivity.
      + simpl in H |- *. exact (IH k' c H).
  Qed.

  Lemma sub_self : forall (a: U256.t), U256.sub a a = U256.zero.
  Proof.
    intros a. unfold U256.sub, U256.zero. rewrite Z.sub_diag. reflexivity.
  Qed.

  Lemma val_zero : U256.val U256.zero = 0%Z.
  Proof.
    reflexivity.
  Qed.

  Lemma mul_zero_l : forall (b: U256.t), U256.mul U256.zero b = U256.zero.
  Proof.
    intros b. unfold U256.mul. rewrite val_zero, Z.mul_0_l. reflexivity.
  Qed.

  Lemma mul_zero_r : forall (a: U256.t), U256.mul a U256.zero = U256.zero.
  Proof.
    intros a. unfold U256.mul. rewrite val_zero, Z.mul_0_r. reflexivity.
  Qed.

  (* an input that is known to be zero evaluates to zero *)
  Lemma known_zero_eval :
    forall (known: VarID.t -> option EVMDialect.value_t) (rho: VarID.t -> EVMDialect.value_t)
           (e: VarID.t + EVMDialect.value_t),
      (forall (v: VarID.t) (c: EVMDialect.value_t), known v = Some c -> rho v = c) ->
      known_zero known e = true ->
      (match e with inl v => rho v | inr c => c end) = U256.zero.
  Proof.
    intros known rho e Hcons H.
    unfold known_zero in H.
    destruct (known_value known e) as [c|] eqn:Hkv; [ | discriminate H].
    apply U256.eqb_eq in H. subst c.
    exact (known_value_eval known rho e U256.zero Hcons Hkv).
  Qed.

  (* a single output, known to be zero *)
  Lemma single_zero_output :
    forall (x: EVMDialect.value_t) (k: nat) (c: EVMDialect.value_t),
      x = U256.zero ->
      nth_error [Some U256.zero] k = Some (Some c) -> nth_error [x] k = Some c.
  Proof.
    intros x k c Hx H.
    destruct k as [| [| k']]; simpl in H |- *; try discriminate H.
    injection H as H. subst c x. reflexivity.
  Qed.

  Lemma abs_exec_partial_snd :
    forall (op: EVMDialect.opcode_t) (es: list (VarID.t + EVMDialect.value_t))
           (known: VarID.t -> option EVMDialect.value_t)
           (res: list (option EVMDialect.value_t)) (st: EVMDialect.dialect_state_t)
           (rho: VarID.t -> EVMDialect.value_t),
      abs_exec_partial op es known = Some res ->
      (forall (v: VarID.t) (c: EVMDialect.value_t), known v = Some c -> rho v = c) ->
      exists (out: list EVMDialect.value_t) (st': EVMDialect.dialect_state_t),
        EVMDialect.execute_opcode st op (List.map (fun e => match e with inl v => rho v | inr c => c end) es)
        = (out, st', Status.Running) /\
        (forall (k: nat) (c: EVMDialect.value_t), nth_error res k = Some (Some c) -> nth_error out k = Some c).
  Proof.
    intros op es known res st rho H Hcons.
    unfold abs_exec_partial in H.
    destruct op; try discriminate H.
    - (* SUB: x - x *)
      destruct es as [| [x|cx] [| [y|cy] [| e3 es']]]; try discriminate H.
      destruct (VarID.eqb x y) eqn:Hxy; [ | discriminate H].
      apply VarID.eqb_eq in Hxy. subst y.
      injection H as H. subst res.
      exists [U256.sub (rho x) (rho x)], st.
      split; [reflexivity | ].
      intros k c Hk. exact (single_zero_output _ k c (sub_self (rho x)) Hk).
    - (* MUL: x * 0 and 0 * x *)
      destruct es as [| e1 [| e2 [| e3 es']]]; try discriminate H.
      destruct (known_zero known e1 || known_zero known e2) eqn:Hz; [ | discriminate H].
      injection H as H. subst res.
      exists [U256.mul (match e1 with inl v => rho v | inr c => c end) (match e2 with inl v => rho v | inr c => c end)], st.
      split; [reflexivity | ].
      intros k c Hk. apply (single_zero_output _ k c); [ | exact Hk].
      apply orb_true_iff in Hz. destruct Hz as [Hz | Hz].
      + pose proof (known_zero_eval known rho e1 Hcons Hz) as He.
        destruct e1; simpl in He |- *; rewrite He; apply mul_zero_l.
      + pose proof (known_zero_eval known rho e2 Hcons Hz) as He.
        destruct e2; simpl in He |- *; rewrite He; apply mul_zero_r.
  Qed.

  Lemma abs_exec_snd :
    forall (op: EVMDialect.opcode_t) (es: list (VarID.t + EVMDialect.value_t))
           (known: VarID.t -> option EVMDialect.value_t)
           (res: list (option EVMDialect.value_t)) (st: EVMDialect.dialect_state_t)
           (rho: VarID.t -> EVMDialect.value_t),
      abs_exec op es known = Some res ->
      (forall (v: VarID.t) (c: EVMDialect.value_t), known v = Some c -> rho v = c) ->
      exists (out: list EVMDialect.value_t) (st': EVMDialect.dialect_state_t),
        EVMDialect.execute_opcode st op (List.map (fun e => match e with inl v => rho v | inr c => c end) es)
        = (out, st', Status.Running) /\
        (forall (k: nat) (c: EVMDialect.value_t), nth_error res k = Some (Some c) -> nth_error out k = Some c).
  Proof.
    intros op es known res st rho H Hcons.
    unfold abs_exec in H.
    destruct (ListFunctions.option_list (List.map (known_value known) es)) as [cs|] eqn:Hl;
      [ | exact (abs_exec_partial_snd op es known res st rho H Hcons)].
    destruct (opcode_indep_state op) eqn:Hind;
      [ | exact (abs_exec_partial_snd op es known res st rho H Hcons)].
    destruct (EVMDialect.execute_opcode empty_state op cs) as [[res0 st0] status0] eqn:Hexec.
    destruct status0;
      try exact (abs_exec_partial_snd op es known res st rho H Hcons).
    (* all inputs known, the opcode is state independent and succeeds *)
    injection H as H. subst res.
    destruct (opcode_indep_state_snd op Hind st empty_state cs) as [r [status [Hst Hempty]]].
    rewrite Hexec in Hempty. injection Hempty as Hr Hs Hstatus. subst r status.
    exists res0, st.
    rewrite (option_list_known_value known rho es cs Hcons Hl).
    split; [exact Hst | ].
    intros k c Hk. exact (map_some_nth_error res0 k c Hk).
  Qed.

End EVMConstSymb.

(* [EVMConstSymb BC] is an abstract execution for [EVMDialect BC], for
any [BC]. (Rocq does not allow writing [<: CONST_SYMB (EVMDialect BC)]
in the header of [EVMConstSymb], since functor arguments must be module
names, so we check it here.) *)
Module EVMConstSymb_check (BC: BLOCK_CHAIN).
  Module ED := EVMDialect(BC).
  Module CS := EVMConstSymb(BC).
  Module Check : CONST_SYMB ED := CS.
End EVMConstSymb_check.
