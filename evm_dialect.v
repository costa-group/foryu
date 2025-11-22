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

  Definition to_U256 (value : U256.t) : U256.t :=
    value mod (2 ^ 256).

  Definition of_bool (b : bool) : U256.t :=
    if b then 1 else 0.

  (* Inspired on Stdlib module from
     https://github.com/formal-land/coq-of-solidity/blob/638c9fdbcbe64e359d337b805a952eb2437ad4ce/coq/CoqOfSolidity/simulations/CoqOfSolidity.v#L408*)
  Definition get_signed_value (value : U256.t) : Z :=
    ((value + (2 ^ 255)) mod (2 ^ 256)) - (2 ^ 255).

  Definition add (a b : U256.t) : U256.t :=
    to_U256 (a + b).

  Definition sub (a b : U256.t) : U256.t :=
    to_U256 (a - b).

  Definition mul (a b : U256.t) : U256.t :=
    to_U256 (a * b).

  Definition div (a b : U256.t) : U256.t :=
    if b =? 0 then 0 else to_U256 (Z.div a b).

  Definition sdiv (x y : U256.t) : U256.t :=
      if y =? 0 then 0
      else
        let x := get_signed_value x in
        let y := get_signed_value y in
        to_U256 (x / y).

  Definition mod_evm (x y : U256.t) : U256.t :=
      if y =? 0 then 0
      else x mod y.

  Definition smod (x y : U256.t) : U256.t :=
      if y =? 0 then 0
      else
        let x := get_signed_value x in
        let y := get_signed_value y in
        to_U256 (x mod y).
    
  Definition exp (x y : U256.t) : U256.t :=
      to_U256 (x ^ y).

  Definition not (x : U256.t) : U256.t :=
      to_U256 (2^256 - x - 1).

  Definition lt (x y : U256.t) : U256.t :=
      if x <? y then 1 else 0.

    Definition gt (x y : U256.t) : U256.t :=
      if x >? y then 1 else 0.

    (* Signed version of [lt] *)
    Definition slt (x y : U256.t) : U256.t :=
      let x := get_signed_value  x in
      let y := get_signed_value  y in
      lt x y.

    Definition sgt (x y : U256.t) : U256.t :=
      let x := get_signed_value x in
      let y := get_signed_value y in
      gt x y.

    Definition eq (x y : U256.t) : U256.t :=
      if x =? y then 1 else 0.

    Definition iszero (x : U256.t) : U256.t :=
      if x =? 0 then 1 else 0.

    Definition and (x y : U256.t) : U256.t :=
      Z.land x y.

    Definition or (x y : U256.t) : U256.t :=
      Z.lor x y.

    Definition xor (x y : U256.t) : U256.t :=
      Z.lxor x y.

    Definition byte (n x : U256.t) : U256.t :=
      (x / (256 ^ (31 - n))) mod 256.  (* SHL and MOD 256 *)

    Definition shl (x y : U256.t) : U256.t :=
      to_U256 (y * (2 ^ x)).

    Definition shr (x y : U256.t) : U256.t :=
      y / (2 ^ x).

    Definition sar (shift value : U256.t) : U256.t :=
      let signed_value := get_signed_value value in
      let shifted_value := signed_value / (2 ^ shift) in
      to_U256 shifted_value.

    Definition addmod (x y m : U256.t) : U256.t :=
      (x + y) mod m.

    Definition mulmod (x y m : U256.t) : U256.t :=
      (x * y) mod m.

    (* From https://github.com/formal-land/coq-of-solidity/blob/638c9fdbcbe64e359d337b805a952eb2437ad4ce/coq/CoqOfSolidity/simulations/CoqOfSolidity.v#L549 *)
    Definition signextend (i x : U256.t) : U256.t :=
      if i >=? 31 then x
      else
        let size := 8 * (i + 1) in
        let byte := (x / 2 ^ (8 * i)) mod 256 in
        let sign_bit := byte / 128 in
        let extend_bit (bit size : Z) : Z :=
          if bit =? 1 then
            (2 ^ 256) - (2 ^ size)
          else
            0 in
        (x mod (2 ^ size)) + extend_bit sign_bit size.

    Definition  eq_dec := Z.eq_dec.

End U256.


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
    .
    
    Definition eq_dec : forall (a b : t), {a = b} + {a <> b}.
      Proof. decide equality. Defined.

    Definition eqb (a b : t) : bool :=
      if eq_dec a b then true else false.
      

    Definition execute (state: EVMState.t) (op: t) (inputs: list U256.t) : (list U256.t * EVMState.t * Status.t) :=
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
      | _  =>  ([42], state, Status.Running) (* FIXME: organize and complete *)
      end. 

End EVM_opcode.


(*
Module Type BLOCK_CHAIN.
  Parameter get_addr : U256.t ->  U256.t.
End BLOCK_CHAIN.
Module EVMDialect (BC: BLOCK_CHAIN) <: DIALECT.

*)

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
    EVM_opcode.execute state op inputs.

  Definition empty_dialect_state : dialect_state :=
    EVMState.empty.

  Definition revert_state (old_state new_state: dialect_state) : dialect_state :=
    old_state.

End EVMDialect.
