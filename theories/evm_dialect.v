Require Import FORYU.dialect.
Require Import FORYU.misc.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Strings.HexString.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Bool.

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
  Defined.
  
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


  (** Count the number of constructors in a positive number *)
  Fixpoint _count_constructors_pos (p: positive): nat :=
    match p with
    | xH => 1
    | xO p' => S (_count_constructors_pos p')
    | xI p' => S (_count_constructors_pos p')
    end.

  (** Count the number of constructors in a Z value *)
  Definition _count_constructors_Z (z: Z): nat :=
    match z with
    | Z0 => 0
    | Zpos p => _count_constructors_pos p
    | Zneg p => _count_constructors_pos p
    end.

  Definition clz (x: U256.t): U256.t :=
    let x_val := val x in
    let len := Z.of_nat (_count_constructors_Z x_val) in
    to_t (256 - len). 

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
  Defined.

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
  Record t : Type := {
    memory : U256.t -> U8.t;
    highest_address: U256.t; (* this is used to track the highest address that has been accessed, which is needed for MSIZE instruction *)
  }.

  Definition empty: t := {|
    memory := fun _ => U8.zero;
    highest_address := U256.zero
  |}.

  Definition msize (memory: t): U256.t :=
    (* The size is always a multiple of a word (32 bytes) *)
    let size := memory.(highest_address) in
    if U256.eqb size U256.zero then U256.zero
    else
      let remainder := U256.mod_evm size (U256.to_t 32) in
      if U256.eqb remainder U256.zero then size
      else U256.add size (U256.sub (U256.to_t 32) remainder).

  Definition update_highest_address (memory: t) (address: U256.t): t :=
    match U256.eqb (U256.gt address memory.(highest_address)) U256.one with
    | true => {| memory := EVMMemory.memory memory; 
                 highest_address := address 
              |}
    | false => memory
    end.

  Definition update_memory (memory: t) (new_memory: U256.t -> U8.t): t :=
    {| memory := new_memory; 
       highest_address := memory.(highest_address) 
    |}.

  (** Get the bytes from some memory from a start address and for a certain length. *)
  Definition get_bytes (memoryt: EVMMemory.t) (start length: U256.t): (list U8.t * EVMMemory.t) :=
    let bytes : list U8.t := List.map
      (fun (i: nat) =>
         let address: U256.t := U256.to_t ((U256.val start) + Z.of_nat i) in (* when reaching end of memory we start from 0 *)
         (EVMMemory.memory memoryt) address
      )
      (List.seq 0 (Z.to_nat (U256.val length))) in
    let memory := update_highest_address memoryt (U256.to_t ((U256.val start) + (U256.val length) - 1)) in
    (bytes, memory).

  Definition update_bytes (memoryt: EVMMemory.t) (start: U256.t) (bytes: list U8.t): EVMMemory.t :=
    let memory := fun address =>
      let i: Z := (U256.val address) - (U256.val start) in
      if andb (0 <=? i) (i <? Z.of_nat (List.length bytes)) then
        List.nth_default U8.zero bytes (Z.to_nat i)
      else
        (EVMMemory.memory memoryt) address in
    let m1 := update_highest_address memoryt (U256.to_t ((U256.val start) + Z.of_nat (List.length bytes) - 1)) in
    let m2 := update_memory m1 memory in
    m2.

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

  Definition length (segment: t): U256.t :=
    U256.to_t (Z.of_nat (List.length segment)).

  (* Returns a list of 'n' bytes from 'start', 0 for bytes out of size *)
  Definition get_bytes (segment: t) (start n: U256.t): list U8.t :=
    List.map
      (fun i =>
         let index: Z := (U256.val start) + Z.of_nat i in
         if index <? Z.of_nat (List.length segment) then
           List.nth_default U8.zero segment (Z.to_nat index)
         else
           U8.zero
      )
      (List.seq 0 (Z.to_nat (U256.val n))).

  Definition get_word (segment: t) (start: U256.t): U256.t :=
    EVMMemory.bytes_as_u256 (get_bytes segment start (U256.to_t 32)).

  Definition hash (segment: t): U256.t :=
    (* TODO: compute actual hash *)
    U256.to_t 42.
    
End EVMMemorySegment.


Module EVMState.
  Record t: Type := {
    storage: EVMStorage.t;
    tstorage: EVMStorage.t; 
    memory: EVMMemory.t;
    call_data_seg: EVMMemorySegment.t;
    return_data_seg: EVMMemorySegment.t;
    gas: U256.t;
    address: U256.t;
    balance: U256.t -> U256.t;
    caller: U256.t;
    callvalue: U256.t;
    code: U256.t -> EVMMemorySegment.t;
    nonce: list U8.t;
    chainid: U256.t;
    basefee: U256.t;
    blobbasefee: U256.t;
    origin: U256.t;
    gasprice: U256.t;
    blockhash: U256.t -> U256.t;
    blobhash: U256.t -> U256.t;
    coinbase: U256.t;
    timestamp: U256.t;
    number: U256.t;
    difficulty: U256.t;
    gaslimit: U256.t;
  }.

  Definition empty: t :=
    {| 
      storage := EVMStorage.empty;
      tstorage := EVMStorage.empty;
      memory := EVMMemory.empty;
      call_data_seg := EVMMemorySegment.empty;
      return_data_seg := EVMMemorySegment.empty;
      gas := U256.zero;
      address := U256.zero;
      balance := fun _ => U256.zero;
      caller := U256.zero;
      callvalue := U256.zero;
      code := fun _ => EVMMemorySegment.empty;
      nonce := [];
      chainid := U256.zero;
      basefee := U256.zero;
      blobbasefee := U256.zero;
      origin := U256.zero;
      gasprice := U256.zero;
      blockhash := fun _ => U256.zero;
      blobhash := fun _ => U256.zero;
      coinbase := U256.zero;
      timestamp := U256.zero;
      number := U256.zero;
      difficulty := U256.zero;
      gaslimit := U256.zero;
    |}.

  Definition update_storage (state: t) (storage' : EVMStorage.t): t :=
  {| 
    storage := storage';
    tstorage := state.(tstorage);
    memory := state.(memory);
    call_data_seg := state.(call_data_seg);
    return_data_seg := state.(return_data_seg);
    gas := state.(gas);
    address := state.(address);
    balance := state.(balance);
    caller := state.(caller);
    callvalue := state.(callvalue);
    code := state.(code);
    nonce := state.(nonce);
    chainid := state.(chainid);
    basefee := state.(basefee);
    blobbasefee := state.(blobbasefee);
    origin := state.(origin);
    gasprice := state.(gasprice);
    blockhash := state.(blockhash);
    blobhash := state.(blobhash);
    coinbase := state.(coinbase);
    timestamp := state.(timestamp);
    number := state.(number);
    difficulty := state.(difficulty);
    gaslimit := state.(gaslimit);
  |}.

  Definition update_tstorage (state: t) (tstorage' : EVMStorage.t): t :=
  {| 
    storage := state.(storage);
    tstorage := tstorage';
    memory := state.(memory);
    call_data_seg := state.(call_data_seg);
    return_data_seg := state.(return_data_seg);
    gas := state.(gas);
    address := state.(address);
    balance := state.(balance);
    caller := state.(caller);
    callvalue := state.(callvalue);
    code := state.(code);
    nonce := state.(nonce);
    chainid := state.(chainid);
    basefee := state.(basefee);
    blobbasefee := state.(blobbasefee);
    origin := state.(origin);
    gasprice := state.(gasprice);
    blockhash := state.(blockhash);
    blobhash := state.(blobhash);
    coinbase := state.(coinbase);
    timestamp := state.(timestamp);
    number := state.(number);
    difficulty := state.(difficulty);
    gaslimit := state.(gaslimit);
  |}.

  Definition update_memory (state: t) (memory' : EVMMemory.t): t :=
  {| 
    storage := state.(storage);
    tstorage := state.(tstorage);
    memory := memory';
    call_data_seg := state.(call_data_seg);
    return_data_seg := state.(return_data_seg); 
    gas := state.(gas);
    address := state.(address);
    balance := state.(balance);
    caller := state.(caller);
    callvalue := state.(callvalue);
    code := state.(code);
    nonce := state.(nonce);
    chainid := state.(chainid);
    basefee := state.(basefee);
    blobbasefee := state.(blobbasefee);
    origin := state.(origin);
    gasprice := state.(gasprice);
    blockhash := state.(blockhash);
    blobhash := state.(blobhash);
    coinbase := state.(coinbase);
    timestamp := state.(timestamp);
    number := state.(number);
    difficulty := state.(difficulty);
    gaslimit := state.(gaslimit);
  |}.

  Definition update_gas (state: t) (gas' : U256.t): t :=
  {| 
    storage := state.(storage);
    tstorage := state.(tstorage);
    memory := state.(memory);
    call_data_seg := state.(call_data_seg);
    return_data_seg := state.(return_data_seg); 
    gas := gas';
    address := state.(address);
    balance := state.(balance);
    caller := state.(caller);
    callvalue := state.(callvalue);
    code := state.(code);
    nonce := state.(nonce);
    chainid := state.(chainid);
    basefee := state.(basefee);
    blobbasefee := state.(blobbasefee);
    origin := state.(origin);
    gasprice := state.(gasprice);
    blockhash := state.(blockhash);
    blobhash := state.(blobhash);
    coinbase := state.(coinbase);
    timestamp := state.(timestamp);
    number := state.(number);
    difficulty := state.(difficulty);
    gaslimit := state.(gaslimit);
  |}.

  Definition update_code (state: t) (addr: U256.t) (ncode: EVMMemorySegment.t): t :=
  {| 
    storage := state.(storage);
    tstorage := state.(tstorage);
    memory := state.(memory);
    call_data_seg := state.(call_data_seg);
    return_data_seg := state.(return_data_seg); 
    gas := state.(gas);
    address := state.(address);
    balance := state.(balance);
    caller := state.(caller);
    callvalue := state.(callvalue);
    code := fun a => if U256.eqb a addr then ncode else (state.(code) a);
    nonce := state.(nonce);
    chainid := state.(chainid);
    basefee := state.(basefee);
    blobbasefee := state.(blobbasefee);
    origin := state.(origin);
    gasprice := state.(gasprice);
    blockhash := state.(blockhash);
    blobhash := state.(blobhash);
    coinbase := state.(coinbase);
    timestamp := state.(timestamp);
    number := state.(number);
    difficulty := state.(difficulty);
    gaslimit := state.(gaslimit);
  |}.

  Definition update_return_data (state: t) (return_data: EVMMemorySegment.t): t :=
  {| 
    storage := state.(storage);
    tstorage := state.(tstorage);
    memory := state.(memory);
    call_data_seg := state.(call_data_seg);
    return_data_seg := return_data;
    gas := state.(gas);
    address := state.(address);
    balance := state.(balance);
    caller := state.(caller);
    callvalue := state.(callvalue);
    code := state.(code);
    nonce := state.(nonce);
    chainid := state.(chainid);
    basefee := state.(basefee);
    blobbasefee := state.(blobbasefee);
    origin := state.(origin);
    gasprice := state.(gasprice);
    blockhash := state.(blockhash);
    blobhash := state.(blobhash);
    coinbase := state.(coinbase);
    timestamp := state.(timestamp);
    number := state.(number);
    difficulty := state.(difficulty);
    gaslimit := state.(gaslimit);
  |}.

  Definition hash (l: list U8.t) : U256.t :=
  (* TODO Compute actual hash *)
    U256.to_t 42.

  Definition invoke (state: t) (gas to value argsOffset argsSize retOffset retSize: U256.t): (U256.t * list U8.t) :=
  (* TODO execute call *)
    (U256.to_t 42, []). (* return value and return data *)

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
    | CLZ
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
    | LINKERSYMBOL
    | SETIMMUTABLE
    | LOADIMMUTABLE
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
      | CLZ => match inputs with
               | [x] => ([U256.clz x], state, Status.Running)
               | _ => ([], state, Status.Error "CLZ expects 1 input")
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
      | KECCAK256 => match inputs with
               | [p; n] => ([U256.to_t 42], state, Status.Running) (* FIXME: implement *)
               | _ => ([], state, Status.Error "KECCAK256 expects 2 inputs")     
               end
      | POP => match inputs with
               | [x] => ([], state, Status.Running)
               | _ => ([], state, Status.Error "POP expects 1 input")
               end
      | MLOAD => match inputs with
                | [addr] => let (bytes, nmemory) := EVMMemory.get_bytes (EVMState.memory state) addr (U256.to_t 32) in
                            let value := EVMMemory.bytes_as_u256 bytes in
                            let new_state := EVMState.update_memory state nmemory in
                            ([value], new_state, Status.Running) 
                | _ => ([], state, Status.Error "MLOAD expects 1 input")
                end
      | MSTORE => match inputs with
                | [addr; value] => let bytes := EVMMemory.u256_as_bytes value in
                                   let new_memory := EVMMemory.update_bytes (EVMState.memory state) addr bytes in
                                   let new_state := EVMState.update_memory state new_memory in
                                   ([], new_state, Status.Running)
                | _ => ([], state, Status.Error "MSTORE expects 2 inputs")
          end
      | MSTORE8 => match inputs with
                | [addr; value] => let byte := U256.mod_evm value (U256.to_t 256) in
                                   let new_memory := EVMMemory.update_bytes (EVMState.memory state) addr [U8.to_t (U256.val byte)] in
                                   let new_state := EVMState.update_memory state new_memory in
                                   ([], new_state, Status.Running)
                | _ => ([], state, Status.Error "MSTORE8 expects 2 inputs")
          end
      | SLOAD => match inputs with
                | [addr] => let value := (EVMState.storage state) addr in
                             ([value], state, Status.Running)
                | _ => ([], state, Status.Error "SLOAD expects 1 input")
          end
      | SSTORE => match inputs with
                | [value; addr] => let new_storage := EVMStorage.update state.(EVMState.storage) addr value in
                                   let new_state := EVMState.update_storage state new_storage in
                                   ([], new_state, Status.Running)
                | _ => ([], state, Status.Error "SSTORE expects 2 inputs")
                end
      | TLOAD => match inputs with
                | [addr] => let value := (EVMState.tstorage state) addr in
                             ([value], state, Status.Running)
                | _ => ([], state, Status.Error "TLOAD expects 1 input")
                end
      | TSTORE => match inputs with
                | [value; addr] => let new_tstorage := EVMStorage.update state.(EVMState.tstorage) addr value in
                                   let new_state := EVMState.update_tstorage state new_tstorage in
                                   ([], new_state, Status.Running)
                | _ => ([], state, Status.Error "TSTORE expects 2 inputs")
                end
      | MSIZE => match inputs with
                | [] => ([EVMMemory.msize (EVMState.memory state)], state, Status.Running)
                | _ => ([], state, Status.Error "MSIZE expects 0 inputs")
                end
      | GAS => match inputs with
                | [] => ([state.(EVMState.gas)], state, Status.Running)
                | _ => ([], state, Status.Error "GAS expects 0 inputs")
                end
      | ADDRESS => match inputs with
                | [] => ([state.(EVMState.address)], state, Status.Running)
                | _ => ([], state, Status.Error "ADDRESS expects 0 inputs")
                end
      | BALANCE => match inputs with
                | [addr] => let balance := state.(EVMState.balance) addr in
                             ([balance], state, Status.Running)
                | _ => ([], state, Status.Error "BALANCE expects 1 input")
                end
      | SELFBALANCE => match inputs with
                | [] => let balance := state.(EVMState.balance) state.(EVMState.address) in
                        ([balance], state, Status.Running)
                | _ => ([], state, Status.Error "SELFBALANCE expects 0 inputs")
                end
      | CALLER => match inputs with
                | [] => ([state.(EVMState.caller)], state, Status.Running)
                | _ => ([], state, Status.Error "CALLER expects 0 inputs")
                end
      | CALLVALUE => match inputs with
                | [] => ([state.(EVMState.callvalue)], state, Status.Running)
                | _ => ([], state, Status.Error "CALLVALUE expects 0 inputs")
                end
      | CALLDATALOAD => match inputs with
                | [offset] => let value := EVMMemorySegment.get_word state.(EVMState.call_data_seg) offset in
                               ([value], state, Status.Running)
                | _ => ([], state, Status.Error "CALLDATALOAD expects 1 input")
                end
      | CALLDATASIZE => match inputs with
                | [] => let size := EVMMemorySegment.length state.(EVMState.call_data_seg) in
                        ([size], state, Status.Running)
                | _ => ([], state, Status.Error "CALLDATASIZE expects 0 inputs")
                end
      | CALLDATACOPY => match inputs with
                | [dest; offset; size] => let bytes := EVMMemorySegment.get_bytes state.(EVMState.call_data_seg) offset size in
                                          let new_memory := EVMMemory.update_bytes (EVMState.memory state) dest bytes in
                                          let new_state := EVMState.update_memory state new_memory in
                                          ([], new_state, Status.Running)
                | _ => ([], state, Status.Error "CALLDATACOPY expects 3 inputs")
                end
      | CODESIZE => match inputs with
                | [] => let code_size := EVMMemorySegment.length (state.(EVMState.code) state.(EVMState.address)) in
                        ([code_size], state, Status.Running)
                | _ => ([], state, Status.Error "CODESIZE expects 0 inputs")
                end
      | CODECOPY => match inputs with
                | [dest; offset; size] => let bytes := EVMMemorySegment.get_bytes (state.(EVMState.code) state.(EVMState.address)) offset size in
                                          let new_memory := EVMMemory.update_bytes (EVMState.memory state) dest bytes in
                                          let new_state := EVMState.update_memory state new_memory in
                                          ([], new_state, Status.Running)
                | _ => ([], state, Status.Error "CODECOPY expects 3 inputs")
                end
      | EXTCODESIZE => match inputs with
                | [addr] => let code_size := EVMMemorySegment.length (state.(EVMState.code) addr) in
                             ([code_size], state, Status.Running)
                | _ => ([], state, Status.Error "EXTCODESIZE expects 1 input")
                end
      | EXTCODECOPY => match inputs with
                | [addr; dest; offset; size] => let bytes := EVMMemorySegment.get_bytes (state.(EVMState.code) addr) offset size in
                                          let new_memory := EVMMemory.update_bytes (EVMState.memory state) dest bytes in
                                          let new_state := EVMState.update_memory state new_memory in
                                          ([], new_state, Status.Running)
                | _ => ([], state, Status.Error "EXTCODECOPY expects 4 inputs")
                end
      | RETURNDATASIZE => match inputs with
                | [] => let size := EVMMemorySegment.length state.(EVMState.return_data_seg) in
                        ([size], state, Status.Running)
                | _ => ([], state, Status.Error "RETURNDATASIZE expects 0 inputs")
                end
      | RETURNDATACOPY => match inputs with
                | [dest; offset; size] => let bytes := EVMMemorySegment.get_bytes state.(EVMState.return_data_seg) offset size in
                                          let new_memory := EVMMemory.update_bytes (EVMState.memory state) dest bytes in
                                          let new_state := EVMState.update_memory state new_memory in
                                          ([], new_state, Status.Running)
                | _ => ([], state, Status.Error "RETURNDATACOPY expects 3 inputs")
                end
      | MCOPY => match inputs with
                | [dest; src; size] => let (bytes, memory') := EVMMemory.get_bytes state.(EVMState.memory) src size in
                                       let new_memory := EVMMemory.update_bytes memory' dest bytes in
                                       let new_state := EVMState.update_memory state new_memory in
                                       ([], new_state, Status.Running)
                | _ => ([], state, Status.Error "MCOPY expects 3 inputs")
                end
      | EXTCODEHASH => match inputs with
                | [addr] => let hash := EVMMemorySegment.hash (state.(EVMState.code) addr) in
                             ([hash], state, Status.Running)
                | _ => ([], state, Status.Error "EXTCODEHASH expects 1 input")
                end
      | CREATE => match inputs with
                | [value; offset; size] => let (code, memory') := EVMMemory.get_bytes (EVMState.memory state) offset size in
                                           let addr := state.(EVMState.address) in 
                                           let addr_u8_list := List.map (fun i => U8.to_t (Z.shiftr (U256.val addr) (8 * (31 - Z.of_nat i)) mod 256)) (List.seq 0 32) in
                                           let addr_l_ext := addr_u8_list ++ state.(EVMState.nonce) in
                                           let naddr := EVMState.hash addr_l_ext in 
                                           let new_state1 := EVMState.update_code state naddr code in
                                           let new_state2 := EVMState.update_memory new_state1 memory' in
                                           ([naddr], new_state2, Status.Running)
                | _ => ([], state, Status.Error "CREATE expects 3 inputs")
                end
      | CREATE2 => match inputs with
                | [value; offset; size; salt] => 
                                           let (code, memory') := EVMMemory.get_bytes (EVMState.memory state) offset size in
                                           let addr := state.(EVMState.address) in 
                                           let addr_u8_list := List.map (fun i => U8.to_t (Z.shiftr (U256.val addr) (8 * (31 - Z.of_nat i)) mod 256)) (List.seq 0 32) in
                                           let salt_u8_list := List.map (fun i => U8.to_t (Z.shiftr (U256.val salt) (8 * (31 - Z.of_nat i)) mod 256)) (List.seq 0 32) in
                                           let addr_l_ext := addr_u8_list ++ salt_u8_list in
                                           let naddr := EVMState.hash addr_l_ext in 
                                           let new_state1 := EVMState.update_code state naddr code in
                                           let new_state2 := EVMState.update_memory new_state1 memory' in
                                           ([naddr], new_state2, Status.Running)
                | _ => ([], state, Status.Error "CREATE2 expects 4 inputs")
                end
      | CALL => match inputs with
                | [gas; to; value; argsOffset; argsSize; retOffset; retSize] => 
                    let (v, return_data) := EVMState.invoke state gas to value argsOffset argsSize retOffset retSize in
                    let new_state := EVMState.update_return_data state return_data in
                    ([v], new_state, Status.Running)
                  | _ => ([], state, Status.Error "CALL expects 7 inputs")
                end
      | CALLCODE => match inputs with
                | [gas; to; value; argsOffset; argsSize; retOffset; retSize] => 
                    let (v, return_data) := EVMState.invoke state gas to value argsOffset argsSize retOffset retSize in
                    let new_state := EVMState.update_return_data state return_data in
                    ([v], new_state, Status.Running)
                  | _ => ([], state, Status.Error "CALLCODE expects 7 inputs")
                end
      | DELEGATECALL => match inputs with
                | [gas; to; argsOffset; argsSize; retOffset; retSize] => 
                    let (v, return_data) := EVMState.invoke state gas to U256.zero argsOffset argsSize retOffset retSize in
                    let new_state := EVMState.update_return_data state return_data in
                    ([v], new_state, Status.Running)
                  | _ => ([], state, Status.Error "DELEGATECALL expects 6 inputs")
                end
      | STATICCALL => match inputs with
                | [gas; to; argsOffset; argsSize; retOffset; retSize] => 
                    let (v, return_data) := EVMState.invoke state gas to U256.zero argsOffset argsSize retOffset retSize in
                    let new_state := EVMState.update_return_data state return_data in
                    ([v], new_state, Status.Running)
                  | _ => ([], state, Status.Error "STATICCALL expects 6 inputs")
                end
      | RETURN => match inputs with
                | [offset; size] => ([], state, Status.Terminated)
                | _ => ([], state, Status.Error "RETURN expects 2 inputs")
                end
      | REVERT => match inputs with
                | [offset; size] => ([], state, Status.Reverted)
                | _ => ([], state, Status.Error "REVERT expects 2 inputs")
                end
      | SELFDESTRUCT => match inputs with
                | [beneficiary] => ([], state, Status.Terminated)
                | _ => ([], state, Status.Error "SELFDESTRUCT expects 1 input")
                end
      | INVALID => ([], state, Status.Error "Invalid opcode")
      | LOG0 => ([], state, Status.Running)
      | LOG1 => ([], state, Status.Running)
      | LOG2 => ([], state, Status.Running)
      | LOG3 => ([], state, Status.Running)
      | LOG4 => ([], state, Status.Running)
      | CHAINID => match inputs with
                | [] => ([state.(EVMState.chainid)], state, Status.Running)
                | _ => ([], state, Status.Error "CHAINID expects 0 inputs")
                end
      | BASEFEE => match inputs with
                | [] => ([state.(EVMState.basefee)], state, Status.Running)
                | _ => ([], state, Status.Error "BASEFEE expects 0 inputs")
                end
      | BLOBBASEFEE => match inputs with
                | [] => ([state.(EVMState.blobbasefee)], state, Status.Running)
                | _ => ([], state, Status.Error "BLOBBASEFEE expects 0 inputs")
                end
      | ORIGIN => match inputs with
                | [] => ([state.(EVMState.origin)], state, Status.Running)
                | _ => ([], state, Status.Error "ORIGIN expects 0 inputs")
                end
      | GASPRICE => match inputs with
                | [] => ([state.(EVMState.gasprice)], state, Status.Running)
                | _ => ([], state, Status.Error "GASPRICE expects 0 inputs")
                end
      | BLOCKHASH => match inputs with
                | [block_number] => let blockhash := state.(EVMState.blockhash) block_number in
                                     ([blockhash], state, Status.Running)
                | _ => ([], state, Status.Error "BLOCKHASH expects 1 input")
                end
      | BLOBHASH => match inputs with
                | [block_number] => let blobhash := state.(EVMState.blobhash) block_number in
                                     ([blobhash], state, Status.Running)
                | _ => ([], state, Status.Error "BLOBHASH expects 1 input")
                end
      | COINBASE => match inputs with
                | [] => ([state.(EVMState.coinbase)], state, Status.Running)
                | _ => ([], state, Status.Error "COINBASE expects 0 inputs")
                end
      | TIMESTAMP => match inputs with
                | [] => ([state.(EVMState.timestamp)], state, Status.Running)
                | _ => ([], state, Status.Error "TIMESTAMP expects 0 inputs")
                end
      | NUMBER => match inputs with
                | [] => ([state.(EVMState.number)], state, Status.Running)
                | _ => ([], state, Status.Error "NUMBER expects 0 inputs")
                end
      | DIFFICULTY => match inputs with
                | [] => ([state.(EVMState.difficulty)], state, Status.Running)
                | _ => ([], state, Status.Error "DIFFICULTY expects 0 inputs")
                end
      | PREVRANDAO => match inputs with
                | [] => ([state.(EVMState.difficulty)], state, Status.Running)
                | _ => ([], state, Status.Error "PREVRANDAO expects 0 inputs")
                end
      | GASLIMIT => match inputs with
                | [] => ([state.(EVMState.gaslimit)], state, Status.Running)
                | _ => ([], state, Status.Error "GASLIMIT expects 0 inputs")
                 end
      | MEMORYGUARD => match inputs with
                | [size] => ([], state, Status.Running) 
                | _ => ([], state, Status.Error "MEMORYGUARD expects 1 input")
                end
      | DATASIZE => match inputs with 
                | [x] => ([], state, Status.Running)
                | _ => ([], state, Status.Error "DATASIZE expects 1 input")
                end
      | DATAOFFSET => match inputs with
                | [x] => ([], state, Status.Running)
                | _ => ([], state, Status.Error "DATAOFFSET expects 1 input")
                end
      | DATACOPY => match inputs with
                | [t; f; l] => ([], state, Status.Running)
                | _ => ([], state, Status.Error "DATACOPY expects 3 inputs")
                end
      | LINKERSYMBOL => match inputs with
                | [library_id] => ([], state, Status.Running)
                | _ => ([], state, Status.Error "LINKERSYMBOL expects 1 inputs")
                end
      | SETIMMUTABLE => match inputs with
                | [offset; name; value] => ([], state, Status.Running)
                | _ => ([], state, Status.Error "SETIMMUTABLE expects 3 inputs")
                end
      | LOADIMMUTABLE => match inputs with
                | [name] => ([], state, Status.Running)  
                | _ => ([], state, Status.Error "LOADIMMUTABLE expects 1 input")
                end 
    end. 

    Definition show (op: t): string :=
      match op with
      | STOP => "STOP"
      | ADD => "ADD"
      | SUB => "SUB"
      | MUL => "MUL"
      | DIV => "DIV"
      | SDIV => "SDIV"
      | MOD => "MOD"
      | SMOD => "SMOD"
      | EXP => "EXP"
      | NOT => "NOT" 
      | LT => "LT"
      | GT => "GT"
      | SLT => "SLT"
      | SGT => "SGT"
      | EQ => "EQ"
      | ISZERO => "ISZERO"
      | AND => "AND"
      | OR => "OR"
      | XOR => "XOR"
      | BYTE => "BYTE"
      | SHL => "SHL"
      | SHR => "SHR"
      | SAR => "SAR"
      | CLZ => "CLZ"
      | ADDMOD => "ADDMOD"
      | MULMOD => "MULMOD"
      | SIGNEXTEND => "SIGNEXTEND"
      | KECCAK256 => "KECCAK256"
      | POP => "POP"
      | MLOAD => "MLOAD"
      | MSTORE => "MSTORE"
      | MSTORE8 => "MSTORE8"
      | SLOAD => "SLOAD"
      | SSTORE => "SSTORE"
      | TLOAD => "TLOAD"
      | TSTORE => "TSTORE"
      | MSIZE => "MSIZE"
      | GAS => "GAS"
      | ADDRESS => "ADDRESS"
      | BALANCE => "BALANCE"
      | SELFBALANCE => "SELFBALANCE"
      | CALLER => "CALLER"
      | CALLVALUE => "CALLVALUE"
      | CALLDATALOAD => "CALLDATALOAD"
      | CALLDATASIZE => "CALLDATASIZE"
      | CALLDATACOPY => "CALLDATACOPY"
      | CODESIZE => "CODESIZE"
      | CODECOPY => "CODECOPY"
      | EXTCODESIZE => "EXTCODESIZE"
      | EXTCODECOPY => "EXTCODECOPY"
      | RETURNDATASIZE => "RETURNDATASIZE"
      | RETURNDATACOPY => "RETURNDATACOPY"
      | MCOPY => "MCOPY"
      | EXTCODEHASH => "EXTCODEHASH"
      | CREATE => "CREATE"
      | CREATE2 => "CREATE2"
      | CALL => "CALL"
      | CALLCODE => "CALLCODE"
      | DELEGATECALL => "DELEGATECALL"
      | STATICCALL => "STATICCALL"
      | RETURN => "RETURN"
      | REVERT => "REVERT"
      | SELFDESTRUCT => "SELFDESTRUCT"
      | INVALID => "INVALID"
      | LOG0 => "LOG0"
      | LOG1 => "LOG1"
      | LOG2 => "LOG2"
      | LOG3 => "LOG3"
      | LOG4 => "LOG4"
      | CHAINID => "CHAINID"
      | BASEFEE => "BASEFEE"
      | BLOBBASEFEE => "BLOBBASEFEE"
      | ORIGIN => "ORIGIN"
      | GASPRICE => "GASPRICE"
      | BLOCKHASH => "BLOCKHASH"
      | BLOBHASH => "BLOBHASH"
      | COINBASE => "COINBASE"
      | TIMESTAMP => "TIMESTAMP"
      | NUMBER => "NUMBER"
      | DIFFICULTY => "DIFFICULTY" (* obsolete from Paris, now uses PREVRANDAO*)
      | PREVRANDAO => "PREVRANDAO"
      | GASLIMIT => "GASLIMIT"
      (**)
      | MEMORYGUARD => "MEMORYGUARD"
      | DATASIZE => "DATASIZE"
      | DATAOFFSET => "DATAOFFSET"
      | DATACOPY => "DATACOPY"
      | LINKERSYMBOL => "LINKERSYMBOL"
      | SETIMMUTABLE => "SETIMMUTABLE"
      | LOADIMMUTABLE => "LOADIMMUTABLE"
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

  Definition dialect_state_t := EVMState.t.

  Definition default_value: value_t := U256.zero.

  Definition execute_opcode (state: dialect_state_t) (op: opcode_t) (inputs: list value_t): (list value_t * dialect_state_t * Status.t) :=
    EVM_opcode.execute state op inputs.

  Definition opcode_indep_state (op: opcode_t) := 
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

  Ltac solve_injection Hexec_s1 Hres Hstatus :=
  injection Hexec_s1 as Hres Hstatus;
  rewrite <- Hres; rewrite <- Hstatus;
  reflexivity.

  Ltac solve_injection_binary arg Hexec_s1 Hres Hstatus :=
  destruct arg; [solve_injection Hexec_s1 Hres Hstatus| ];
  destruct arg; [solve_injection Hexec_s1 Hres Hstatus| ];
  destruct arg; [solve_injection Hexec_s1 Hres Hstatus| solve_injection Hexec_s1 Hres Hstatus].

  Ltac solve_injection_ternary arg Hexec_s1 Hres Hstatus :=
  destruct arg; [solve_injection Hexec_s1 Hres Hstatus| ];
  destruct arg; [solve_injection Hexec_s1 Hres Hstatus| ];
  destruct arg; [solve_injection Hexec_s1 Hres Hstatus| ];
  destruct arg; [solve_injection Hexec_s1 Hres Hstatus| solve_injection Hexec_s1 Hres Hstatus].

  Lemma evm_opcode_indep_state_snd: forall (s1 s2: dialect_state_t) (op: opcode_t) (args: list value_t)
       (res: list value_t) (status: Status.t), 
    opcode_indep_state op = true -> 
    execute_opcode s1 op args = (res, s1, status) ->
    execute_opcode s2 op args = (res, s2, status).
  Proof.
    unfold execute_opcode. unfold EVM_opcode.execute.
    intros s1 s2 op arg res status Hopcode Hexec_s1.
    destruct op; try (simpl in Hopcode; discriminate Hopcode); (* dependent opcode, trivial *)
                 try (solve_injection_binary arg Hexec_s1 Hres Hstatus);
                 try (solve_injection_ternary arg Hexec_s1 Hres Hstatus).
  Qed.
  
  Definition opcode_indep_state_snd := evm_opcode_indep_state_snd.

  Definition empty_dialect_state: dialect_state_t :=
    EVMState.empty.

  Definition show_value (v: value_t): string :=
    Misc.z_to_string (v.(U256.val)).
  
  Definition show_opcode (op: opcode_t): string :=
    EVM_opcode.show op.

End EVMDialect.

Module EVMDialect_Facts := DialectFacts EVMDialect.
