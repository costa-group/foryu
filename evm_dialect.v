Require Export FORYU.dialect.
Require Export Coq.ZArith.ZArith.
Global Open Scope Z_scope.
Require Export Coq.Lists.List.
Import ListNotations.
Require Coq.Strings.HexString.
Require Export Coq.Strings.String.




Module U256.
  Definition t := Z.

  Module Valid.
    Definition t (value : U256.t) : Prop :=
      0 <= value < 2 ^ 256.
  End Valid.

  Definition of_bool (b : bool) : U256.t :=
    if b then 1 else 0.
End U256.


Module EVM_opcode.
  Inductive t :=
    | ADD
    | MUL
    | SUB
    | DIV
    | SDIV
    | MOD
    | SMOD
    | ADDMOD
    | MULMOD
    | EXP
    | SIGNEXTEND
    | LT
    | GT
    | SLT
    | SGT
    | EQ
    | ISZERO
    | AND
    | OR
    | XOR
    | NOT
    | BYTE
    | SHL
    | SHR
    | SAR
    | ADDRESS
    | BALANCE
    | ORIGIN
    | CALLER
    | CALLVALUE
    | CALLDATALOAD
    | CALLDATASIZE
    | CODESIZE
    | GASPRICE
    | EXTCODESIZE
    | RETURNDATASIZE
    | EXTCODEHASH
    | BLOCKHASH
    | COINBASE
    | TIMESTAMP
    | NUMBER
    | DIFFICULTY
    | GASLIMIT
    | CHAINID
    | SELFBALANCE
    | BASEFEE
    | GAS
    | JUMPI. (* This is implemented with a different semantics!! It does not really jump. We need it to handle blocks that end with JUMPI but their corresponding optimized one ends with JMP *)

    Definition eq_dec : forall (a b : t), {a = b} + {a <> b}.
      Proof. decide equality. Defined.

    Definition eqb (a b : t) : bool :=
      if eq_dec a b then true else false.

End EVM_opcode.


Module EVMStorage.
  (* From github.com/formal-land/coq-of-solidity/blob/develop/coq/CoqOfSolidity/simulations/CoqOfSolidity.v 
  *)
  Definition t : Set :=
    U256.t -> U256.t.

  Definition empty : t :=
    fun _ => 0.

  Definition update (storage : EVMStorage.t) (address value : U256.t) : EVMStorage.t :=
    fun current_address =>
      if address =? current_address then
        value
      else
        storage current_address.
End EVMStorage.


Module EVMMemory.
  (** From 
      github.com/formal-land/coq-of-solidity/blob/develop/coq/CoqOfSolidity/simulations/CoqOfSolidity.v 
  *)
  (** We define the memory as a function instead of an explicit list as there can be holes in it. It
      goes from addresses in [U256.t] to bytes represented as [Z]. *)
  Definition t : Type :=
    U256.t -> Z.

  Definition empty : t :=
    fun _ => 0.

  (** Get the bytes from some memory from a start adress and for a certain length. *)
  Definition get_bytes (memory : EVMMemory.t) (start length : U256.t) : list Z :=
    List.map
      (fun (i : nat) =>
        let address : U256.t := start + Z.of_nat i in
        memory address
      )
      (List.seq 0 (Z.to_nat length)).

  Definition update_bytes (memory : EVMMemory.t) (start : U256.t) (bytes : list Z) : EVMMemory.t :=
    fun address =>
      let i : Z := address - start in
      if andb (0 <=? i) (i <? Z.of_nat (List.length bytes)) then
        List.nth_default 0 bytes (Z.to_nat i)
      else
        memory address.

  Definition u256_as_bytes (value : U256.t) : list Z :=
    List.map
      (fun (i : nat) => Z.shiftr value (8 * (31 - Z.of_nat i)) mod 256)
      (List.seq 0 32).

  Fixpoint bytes_as_u256_aux (acc : Z) (bytes : list Z) : U256.t :=
    match bytes with
    | [] => acc
    | byte :: bytes =>
      bytes_as_u256_aux
        (acc * 256 + byte)
        bytes
    end.

  Definition bytes_as_u256 (bytes : list Z) : U256.t :=
    bytes_as_u256_aux 0 bytes.

  Lemma bytes_as_u256_bounds (bytes : list Z)
      (H_bytes : List.Forall (fun byte => 0 <= byte < 256) bytes) :
    0 <= bytes_as_u256 bytes < 2 ^ (8 * Z.of_nat (List.length bytes)).
  Proof.
  Admitted.

  (*
  Definition bytes_as_bytes (bytes : list Z) : list Nibble.byte :=
    List.map
      (fun (byte : Z) => Nibble.byte_of_N (Z.to_N byte))
      bytes.
  *)

  Fixpoint hex_string_as_bytes (hex_string : string) : list Z :=
    match hex_string with
    | ""%string => []
    | String.String a "" => [] (* this case is unexpected *)
    | String.String a (String.String b rest) =>
      match HexString.ascii_to_digit a, HexString.ascii_to_digit b with
      | Some a, Some b =>
        let byte := 16 * Z.of_N a + Z.of_N b in
        byte :: hex_string_as_bytes rest
      | _, _ => [] (* this case is unexpected *)
      end
    end.
End EVMMemory.


Module EVMMemorySegment.
  (** List of bytes represented as Z. *)
  Definition t : Type := list Z.
  Definition empty : t := [].
End EVMMemorySegment.


Module EVMState.
  Record t : Type := {
    storage : EVMStorage.t;
    memory: EVMMemory.t;
    call_data_seg : EVMMemorySegment.t;
    return_data_seg: EVMMemorySegment.t;
  }.

  Definition empty : t :=
    {| 
      storage := EVMStorage.empty;
      memory := EVMMemory.empty;
      call_data_seg := EVMMemorySegment.empty;
      return_data_seg := EVMMemorySegment.empty;
    |}.
End EVMState.





Module EVMDialect <: DIALECT.
  Definition value_t := U256.t.
  Definition opcode_t := EVM_opcode.t.
  Definition dialect_state := EVMState.t.

  Definition default_value : value_t := 0.
  Definition is_true_value (v: value_t) : bool :=
    v =? 0.
  Definition is_false_value (v: value_t) : bool :=
    negb (is_true_value v).
  Definition equal_values (v1 v2: value_t) : bool :=
    v1 =? v2.

  Definition execute_op_code (state: dialect_state) (op: opcode_t) (inputs: list value_t) : (list value_t * dialect_state * Status.t) :=
    ([default_value], state, Status.Running). (* Placeholder for actual implementation *)

  Definition empty_dialect_state : dialect_state :=
    EVMState.empty.

  Definition revert_state (old_state new_state: dialect_state) : dialect_state :=
    old_state.
End EVMDialect.
