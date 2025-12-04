Require Import FORYU.dialect.
Require Import FORYU.misc.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Require Coq.Strings.HexString.
Require Import Coq.Strings.String.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Bool.

Open Scope Z_scope. (* Important: Makes '+' refer to Z.add *)

(* An arithmetic modulo 2^256 that is based on Z *)
Module U256.

  Definition modulus := 2^256.
  
  Definition Valid (val: Z): Prop :=
    0 <= val < modulus.
  
  (* The Type Definition. It includes the value and a proposition stating its validity *)
  Record t := mk {
    val : Z;
    is_valid : Valid val
  }.

  Definition eqb (x y: t): bool :=
    Z.eqb (val x) (val y).

  (* we require boolean equality to reflect equality *)
  Lemma eqb_spec : forall x y : t, reflect (x = y) (eqb x y).
  Proof.
    intros x y.
    unfold eqb.

    destruct (Z.eqb_spec (val x) (val y)) as [Heq | Hneq].

    - apply ReflectT.
      destruct x as [vx px], y as [vy py].
      simpl in Heq.
      subst vy.
      f_equal.
      apply proof_irrelevance.

    - apply ReflectF.
      intro H_assume_equal.
      rewrite H_assume_equal in Hneq.
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
  
  
  (* A constructor that takes any Z and fits it into t *)
  Program Definition to_t (z : Z) : t :=
    mk (z mod modulus) _.
  Next Obligation.
    apply Z.mod_pos_bound.
    vm_compute. reflexivity.
  Defined.

  Definition zero: t := to_t 0.
  Definition one: t := to_t 1.
  Definition two_to_255: t := to_t (2^255).
  
  
  Definition of_bool (b: bool): U256.t :=
    if b then one else zero.

  (* Inspired by Stdlib module of
     https://github.com/formal-land/coq-of-solidity/blob/638c9fdbcbe64e359d337b805a952eb2437ad4ce/coq/CoqOfSolidity/simulations/CoqOfSolidity.v#L408*)
  Definition get_signed_value (value: U256.t): Z :=
    (((val value) + (2 ^ 255)) mod (2 ^ 256)) - (2 ^ 255).

  Definition add (a b: U256.t): U256.t :=
    to_t ( (val a) + (val b) ).

  Definition sub (a b: U256.t): U256.t :=
    to_t ( (val a) - (val b) ).

  Definition mul (a b: U256.t): U256.t :=
    to_t ( (val a) * (val b) ).

  Definition div (a b: U256.t): U256.t :=
    if (val b) =? 0 then zero else to_t (Z.div (val a) (val b)).

  Definition sdiv (x y: U256.t): U256.t :=
      if (val y) =? 0 then zero
      else
        let zx := get_signed_value x in
        let zy := get_signed_value y in
        to_t (zx / zy).

  Definition mod_evm (x y: U256.t): U256.t :=
      if (val y) =? 0 then zero
      else to_t ((val x) mod (val y)). (* this could be improved to eliminate the call to to_t *)

  Definition smod (x y: U256.t): U256.t :=
      if (val y) =? 0 then zero
      else
        let x := get_signed_value x in
        let y := get_signed_value y in
        to_t (x mod y).
    
  Definition exp (x y: U256.t): U256.t :=
      to_t ((val x) ^ (val y)).

  Definition not (x: U256.t): U256.t :=
      to_t (2^256 - (val x) - 1).

  Definition lt (x y: U256.t): U256.t :=
      if (val x) <? (val y) then one else zero.

  Definition gt (x y: U256.t): U256.t :=
    if (val x) >? (val y) then one else zero.

  (* Signed version of [lt] *)
  Definition slt (x y: U256.t): U256.t :=
    let x := get_signed_value x in
    let y := get_signed_value y in
    if x <? y then one else zero.
  
  Definition sgt (x y: U256.t): U256.t :=
    let x := get_signed_value x in
    let y := get_signed_value y in
    if x >?  y then one else zero.

  Definition eq (x y: U256.t): U256.t :=
    if (val x) =? (val y) then one else zero.
  
  Definition iszero (x: U256.t): U256.t :=
    if (val x) =? 0 then one else zero.
  
  Definition and (x y: U256.t): U256.t :=
    to_t (Z.land (val x) (val y)). (* this could be improved to eliminate the call to to_t *)

  Definition or (x y: U256.t): U256.t :=
    to_t (Z.lor (val x) (val y)).

  Definition xor (x y: U256.t): U256.t :=
    to_t (Z.lxor (val x) (val y)).

  Definition byte (n x: U256.t): U256.t := (* SHL and MOD 256 *)
    to_t ( ( (val x) / (256 ^ (31 - (val n)))) mod 256). (* this could be improved to eliminate the call to to_t *)

  Definition shl (x y: U256.t): U256.t :=
    to_t ((val y) * (2 ^ (val x))).

  Definition shr (x y: U256.t): U256.t :=
    to_t ((val y) / (2 ^ (val x))). (* this could be improved to eliminate the call to to_t *)

  Definition sar (shift value: U256.t): U256.t :=
    let signed_value := get_signed_value value in
    let shifted_value := signed_value / (2 ^ (val shift)) in
    to_t shifted_value.

  Definition addmod (x y m: U256.t): U256.t :=
    to_t ( ((val x) + (val y)) mod (val m) ). (* this could be improved to eliminate the call to to_t *)

  Definition mulmod (x y m: U256.t): U256.t :=
   to_t ( ((val x) * (val y)) mod (val m)). (* this could be improved to eliminate the call to to_t *)

    (* From https://github.com/formal-land/coq-of-solidity/blob/638c9fdbcbe64e359d337b805a952eb2437ad4ce/coq/CoqOfSolidity/simulations/CoqOfSolidity.v#L549 *)
  Definition signextend (ai ax: U256.t): U256.t :=
    let i := (val ai) in
    let x := (val ax) in
    if i >=? 31 then ax
    else
      let size := 8 * (i + 1) in
      let byte := (x / 2 ^ (8 * i)) mod 256 in
      let sign_bit := byte / 128 in
      let extend_bit (bit size: Z): Z := if bit =? 1 then (2 ^ 256) - (2 ^ size) else 0 in
      to_t ((x mod (2 ^ size)) + extend_bit sign_bit size). (* this could be improved to eliminate the call to to_t *)

End U256.


(* A byte *)
Module U8.

  Definition modulus := 2^8.
  
  Definition Valid (val: Z): Prop :=
    0 <= val < modulus.

  
  (* The Type Definition. It includes the value and a proposition stating its validity *)
  Record t := mk {
    val : Z;
    is_valid : Valid val
  }.

  (* A constructor that takes any Z and fits it into t *)
  Program Definition to_t (z : Z) : t :=
    mk (z mod modulus) _.
  Next Obligation.
    apply Z.mod_pos_bound.
    vm_compute. reflexivity.
  Definition.

  Definition zero: t := to_t 0.
  Definition one: t := to_t 1.

End U8.

Module EVMStorage.
  (* From github.com/formal-land/coq-of-solidity/blob/develop/coq/CoqOfSolidity/simulations/CoqOfSolidity.v 
  *)
  Definition t: Set :=
    U256.t -> U256.t.

  Definition empty: t :=
    fun _ => U256.zero.

  Definition update (storage: EVMStorage.t) (address value: U256.t): EVMStorage.t :=
    fun current_address =>
      if U256.eqb address current_address then value
      else storage current_address.
End EVMStorage.


Module EVMMemory.
  (** From 
      github.com/formal-land/coq-of-solidity/blob/develop/coq/CoqOfSolidity/simulations/CoqOfSolidity.v 
  *)
  (** We define the memory as a function instead of an explicit list as there can be holes in it. It
      goes from addresses in [U256.t] to bytes represented as [Z]. *)
  Definition t: Type :=
    U256.t -> U8.t.

  Definition empty: t :=
    fun _ => U8.zero.

  (** Get the bytes from some memory from a start adress and for a certain length. *)
  Definition get_bytes (memory: EVMMemory.t) (start length: U256.t): list U8.t :=
    List.map
      (fun (i: nat) =>
         let address: U256.t := U256.to_t ((U256.val start) + Z.of_nat i) in (* when reaching end of memory we start from 0 *)
         memory address
      )
      (List.seq 0 (Z.to_nat (U256.val length))).

  Definition update_bytes (memory: EVMMemory.t) (start: U256.t) (bytes: list U8.t): EVMMemory.t :=
    fun address =>
      let i: Z := (U256.val address) - (U256.val start) in
      if andb (0 <=? i) (i <? Z.of_nat (List.length bytes)) then
        List.nth_default U8.zero bytes (Z.to_nat i)
      else
        memory address.

  Definition u256_as_bytes (value: U256.t): list U8.t :=
    List.map
      (fun (i: nat) => U8.to_t (Z.shiftr (U256.val value) (8 * (31 - Z.of_nat i)) mod 256) )
      (List.seq 0 32).

  Fixpoint bytes_as_u256_aux (acc: Z) (bytes: list U8.t): U256.t :=
    match bytes with
    | [] => U256.to_t acc
    | byte :: bytes =>
      bytes_as_u256_aux
        (acc * 256 + (U8.val byte))
        bytes
    end.

  Definition bytes_as_u256 (bytes: list U8.t): U256.t :=
    bytes_as_u256_aux 0 bytes.

  (*
  Lemma bytes_as_u256_bounds (bytes: list U8.t):
    0 <= bytes_as_u256 bytes < 2 ^ (8 * Z.of_nat (List.length bytes)).
  Proof.
  Admitted.
   *)
  
  Fixpoint hex_string_as_bytes (hex_string: string): list U8.t :=
    match hex_string with
    | ""%string => []
    | String.String a "" => [] (* this case is unexpected *)
    | String.String a (String.String b rest) =>
      match HexString.ascii_to_digit a, HexString.ascii_to_digit b with
      | Some a, Some b =>
        let byte := 16 * Z.of_N a + Z.of_N b in
        (U8.to_t byte):: hex_string_as_bytes rest
      | _, _ => [] (* this case is unexpected *)
      end
    end.
End EVMMemory.


Module EVMMemorySegment.
  (** List of bytes represented as Z. *)
  Definition t: Type := list U8.t.
  Definition empty: t := [].
End EVMMemorySegment.


Module EVMState.
  Record t: Type := {
    storage: EVMStorage.t;
    memory: EVMMemory.t;
    call_data_seg: EVMMemorySegment.t;
    return_data_seg: EVMMemorySegment.t;
  }.

  Definition empty: t :=
    {| 
      storage := EVMStorage.empty;
      memory := EVMMemory.empty;
      call_data_seg := EVMMemorySegment.empty;
      return_data_seg := EVMMemorySegment.empty;
    |}.
End EVMState.


Module EVM_opcode.
  Inductive t :=
    | STOP
    | ADD
    | SUB
    | MUL
    | DIV
    | SDIV
    | MOD
    | SMOD
    | EXP
    | NOT 
    | LT
    | GT
    | SLT
    | SGT
    | EQ
    | ISZERO
    | AND
    | OR
    | XOR
    | BYTE
    | SHL
    | SHR
    | SAR
    | ADDMOD
    | MULMOD
    | SIGNEXTEND
    | KECCAK256
    | POP
    | MLOAD
    | MSTORE
    | MSTORE8
    | SLOAD
    | SSTORE
    | TLOAD
    | TSTORE
    | MSIZE
    | GAS
    | ADDRESS
    | BALANCE
    | SELFBALANCE
    | CALLER
    | CALLVALUE
    | CALLDATALOAD
    | CALLDATASIZE
    | CALLDATACOPY
    | CODESIZE
    | CODECOPY
    | EXTCODESIZE
    | EXTCODECOPY
    | RETURNDATASIZE
    | RETURNDATACOPY
    | MCOPY
    | EXTCODEHASH
    | CREATE 
    | CREATE2
    | CALL
    | CALLCODE
    | DELEGATECALL
    | STATICCALL
    | RETURN
    | REVERT
    | SELFDESTRUCT
    | INVALID
    | LOG0
    | LOG1
    | LOG2
    | LOG3
    | LOG4
    | CHAINID
    | BASEFEE
    | BLOBBASEFEE
    | ORIGIN
    | GASPRICE
    | BLOCKHASH
    | BLOBHASH
    | COINBASE
    | TIMESTAMP
    | NUMBER
    | DIFFICULTY  (* obsolete from Paris, now uses PREVRANDAO*)
    | PREVRANDAO
    | GASLIMIT

    | MEMORYGUARD
    | DATASIZE
    | DATAOFFSET
    | DATACOPY
    .
    
    Definition eq_dec: forall (a b: t), {a = b} + {a <> b}.
      Proof. decide equality. Defined.

    Definition eqb (a b: t): bool :=
      if eq_dec a b then true else false.
      

    Definition execute (state: EVMState.t) (op: t) (inputs: list U256.t): (list U256.t * EVMState.t * Status.t) :=
      match op with
      | STOP => ([], state, Status.Terminated)
      | ADD => match inputs with
               | [x; y] => ([U256.add x y], state, Status.Running)
               | _ => ([], state, Status.Error "ADD expects 2 inputs")
               end
      | SUB => match inputs with
               | [x; y] => ([U256.sub x y], state, Status.Running)
               | _ => ([], state, Status.Error "SUB expects 2 inputs")
               end
      | MUL => match inputs with
               | [x; y] => ([U256.mul x y], state, Status.Running)
               | _ => ([], state, Status.Error "MUL expects 2 inputs")
               end
      | DIV => match inputs with
               | [x; y] => ([U256.div x y], state, Status.Running)
               | _ => ([], state, Status.Error "DIV expects 2 inputs")
               end
      | SDIV => match inputs with
               | [x; y] => ([U256.sdiv x y], state, Status.Running)
               | _ => ([], state, Status.Error "SDIV expects 2 inputs")
               end
      | MOD => match inputs with
               | [x; y] => ([U256.mod_evm x y], state, Status.Running)
               | _ => ([], state, Status.Error "MOD expects 2 inputs")
               end
      | SMOD => match inputs with
               | [x; y] => ([U256.smod x y], state, Status.Running)
               | _ => ([], state, Status.Error "SMOD expects 2 inputs")
               end
      | EXP => match inputs with
               | [x; y] => ([U256.exp x y], state, Status.Running)
               | _ => ([], state, Status.Error "EXP expects 2 inputs")
               end  
      | NOT => match inputs with
               | [x] => ([U256.not x], state, Status.Running)
               | _ => ([], state, Status.Error "NOT expects 1 input")
               end
      | LT => match inputs with 
               | [x; y] => ([U256.lt x y], state, Status.Running)
               | _ => ([], state, Status.Error "LT expects 2 inputs")
               end
      | GT => match inputs with
               | [x; y] => ([U256.gt x y], state, Status.Running)
               | _ => ([], state, Status.Error "GT expects 2 inputs")
               end
      | SLT => match inputs with
               | [x; y] => ([U256.slt x y], state, Status.Running)
               | _ => ([], state, Status.Error "SLT expects 2 inputs")
               end
      | SGT => match inputs with
               | [x; y] => ([U256.sgt x y], state, Status.Running)
               | _ => ([], state, Status.Error "SGT expects 2 inputs")
               end  
      | EQ => match inputs with
               | [x; y] => ([U256.eq x y], state, Status.Running)
               | _ => ([], state, Status.Error "EQ expects 2 inputs")
               end
      | ISZERO => match inputs with
               | [x] => ([U256.iszero x], state, Status.Running)
               | _ => ([], state, Status.Error "ISZERO expects 1 input")
               end
      | AND => match inputs with
               | [x; y] => ([U256.and x y], state, Status.Running)
               | _ => ([], state, Status.Error "AND expects 2 inputs")
               end
      | OR => match inputs with
               | [x; y] => ([U256.or x y], state, Status.Running)
               | _ => ([], state, Status.Error "OR expects 2 inputs")
               end
      | XOR => match inputs with
               | [x; y] => ([U256.xor x y], state, Status.Running)
               | _ => ([], state, Status.Error "XOR expects 2 inputs")
               end  
      | BYTE => match inputs with
               | [n; x] => ([U256.byte n x], state, Status.Running)
               | _ => ([], state, Status.Error "BYTE expects 2 inputs")
               end
      | SHL => match inputs with
               | [x; y] => ([U256.shl x y], state, Status.Running)
               | _ => ([], state, Status.Error "SHL expects 2 inputs")
               end
      | SHR => match inputs with
               | [x; y] => ([U256.shr x y], state, Status.Running)
               | _ => ([], state, Status.Error "SHR expects 2 inputs")
               end
      | SAR => match inputs with
               | [x; y] => ([U256.sar x y], state, Status.Running)
               | _ => ([], state, Status.Error "SAR expects 2 inputs")
               end
      | ADDMOD => match inputs with
               | [x; y; m] => ([U256.addmod x y m], state, Status.Running)
               | _ => ([], state, Status.Error "ADDMOD expects 3 inputs")
               end
      | MULMOD => match inputs with
               | [x; y; m] => ([U256.mulmod x y m], state, Status.Running)
               | _ => ([], state, Status.Error "MULMOD expects 3 inputs")
               end
      | SIGNEXTEND => match inputs with
               | [i; x] => ([U256.signextend i x], state, Status.Running)
               | _ => ([], state, Status.Error "SIGNEXTEND expects 2 inputs")
               end
               
      | SSTORE => 
          match inputs with
          | value ::addr :: nil =>
              let new_storage := EVMStorage.update state.(EVMState.storage) addr value in
              let new_state := {| EVMState.storage := new_storage;
                                  EVMState.memory := state.(EVMState.memory);
                                  EVMState.call_data_seg := state.(EVMState.call_data_seg);
                                  EVMState.return_data_seg := state.(EVMState.return_data_seg) |} in
              ([], new_state, Status.Running)
          | _ => ([], state, Status.Error "SSTORE expects 2 inputs")
          end
      | _  =>  ([U256.to_t 42], state, Status.Running) (* FIXME: organize and complete *)
      end. 

End EVM_opcode.


(*
Module Type BLOCK_CHAIN.
  Parameter get_addr: U256.t ->  U256.t.
End BLOCK_CHAIN.
Module EVMDialect (BC: BLOCK_CHAIN) <: DIALECT.

*)

Module EVMDialect <: DIALECT.
  Definition value_t := U256.t.

  Definition eqb := U256.eqb.
  Definition eqb_spec := U256.eqb_spec.

  Definition is_true_value (v: value_t): bool :=
    U256.eqb v U256.zero. (* 0 or 1? *)

  Definition opcode_t := EVM_opcode.t.

  Definition dialect_state := EVMState.t.

  Definition default_value: value_t := U256.zero.

  Definition execute_op_code (state: dialect_state) (op: opcode_t) (inputs: list value_t): (list value_t * dialect_state * Status.t) :=
    EVM_opcode.execute state op inputs.

  Definition empty_dialect_state: dialect_state :=
    EVMState.empty.
    

End EVMDialect.

Module EVMDialect_Facts := DialectFacts EVMDialect.
