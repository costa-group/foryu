Require Export Coq.ZArith.ZArith.
Require Coq.Strings.HexString.
Require Export Coq.Strings.String.
Require Import List.
Import ListNotations.

From Ltac2 Require Ltac2.
Require Export Lia.
From Hammer Require Export Tactics.

Require Import FORYU.program.

Global Open Scope string_scope.
Global Open Scope Z_scope.
(* Global Open Scope list_scope. *)

(*

Module U256.
  Definition t := Z.

  Module Valid.
    Definition t (value : U256.t) : Prop :=
      0 <= value < 2 ^ 256.
  End Valid.

  Definition of_bool (b : bool) : U256.t :=
    if b then 1 else 0.
End U256.

Module Address.
  (** This type is a synonym and acts mainly as documentation purpose. *)
  Definition t : Set := U256.t.

  Module Valid.
    Definition t (address : Address.t) : Prop :=
      0 <= address < 2 ^ 160.
  End Valid.
End Address.

Module Environment.
  Record t : Set := {
    caller : U256.t;
    (** Amount of wei sent to the current contract *)
    callvalue : U256.t;
    calldata : list Z;
    (** The address of the contract. *)
    address : U256.t;
    (** The name of the current code that is being executed. *)
    code_name : U256.t;
  }.
End Environment.

Module BlockUnit.
  (** The return value of a code block. *)
  Inductive t : Set :=
  (** The default value in case of success *)
  | Tt
  (** The instruction `break` was called *)
  | Break
  (** The instruction `continue` was called *)
  | Continue
  (** The instruction `leave` was called *)
  | Leave.
End BlockUnit.

Module Result.
  (** A wrapper for the result of an expression or a code block. We can either return a normal value
      with [Ok], or a special instruction [Return] that will stop the execution of the contract. *)
  Inductive t (A : Set) : Set :=
  | Ok (output : A)
  | Return (p s : U256.t)
  | Revert (p s : U256.t).
  Arguments Ok {_}.
  Arguments Return {_}.
  Arguments Revert {_}.

  Definition map {A B : Set} (f : A -> B) (value : t A) : t B :=
    match value with
    | Ok output => Ok (f output)
    | Return p s => Return p s
    | Revert p s => Revert p s
    end.
End Result.

Module Memory.
  (** We define the memory as a function instead of an explicit list as there can be holes in it. It
      goes from addresses in [U256.t] to bytes represented as [Z]. *)
  Definition t : Set :=
    U256.t -> Z.

  Definition empty : t :=
    fun _ => 0.

  (** Get the bytes from some memory from a start adress and for a certain length. *)
  Definition get_bytes (memory : Memory.t) (start length : U256.t) : list Z :=
    List.map
      (fun (i : nat) =>
        let address : U256.t := start + Z.of_nat i in
        memory address
      )
      (List.seq 0 (Z.to_nat length)).

  Definition update_bytes (memory : Memory.t) (start : U256.t) (bytes : list Z) : Memory.t :=
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
    | byte :: bytes => bytes_as_u256_aux (acc * 256 + byte) bytes
    end.

  Definition bytes_as_u256 (bytes : list Z) : U256.t :=
    bytes_as_u256_aux 0 bytes.

  Lemma bytes_as_u256_bounds (bytes : list Z)
      (H_bytes : List.Forall (fun byte => 0 <= byte < 256) bytes) :
    0 <= bytes_as_u256 bytes < 2 ^ (8 * Z.of_nat (List.length bytes)).
  Proof.
  Admitted.

  (* Definition bytes_as_bytes (bytes : list Z) : list Nibble.byte :=
    List.map
      (fun (byte : Z) => Nibble.byte_of_N (Z.to_N byte))
      bytes.
  *)

  Fixpoint hex_string_as_bytes (hex_string : string) : list Z :=
    match hex_string with
    | "" => []
    | String.String a "" => [] (* this case is unexpected *)
    | String.String a (String.String b rest) =>
      match HexString.ascii_to_digit a, HexString.ascii_to_digit b with
      | Some a, Some b =>
        let byte := 16 * Z.of_N a + Z.of_N b in
        byte :: hex_string_as_bytes rest
      | _, _ => [] (* this case is unexpected *)
      end
    end.
End Memory.

Module Storage.
  (** Each slot in the storage is a word. This is different from [Memory.t] where it is only
      bytes. *)
  Definition t : Set :=
    U256.t -> U256.t.

  Definition empty : t :=
    fun _ => 0.

  Definition update (storage : Storage.t) (address value : U256.t) : Storage.t :=
    fun current_address =>
      if address =? current_address then
        value
      else
        storage current_address.
End Storage.

Module CallStack.
  (** The list of functions that were called with their corresponding parameters. This is for
      debugging purpose only, and does not exist in the semantics of Yul. *)
  Definition t : Set :=
    list (string * list (string * U256.t)).
End CallStack.

Module Dict.
  Definition t (K V : Set) : Set :=
    list (K * V).

  Module Valid.
    Definition t {K V : Set} (P_K : K -> Prop) (P_V : V -> Prop) (dict : Dict.t K V) : Prop :=
      List.Forall (fun '(k, v) => P_K k /\ P_V v) dict.
  End Valid.

  Module Eq.
    Class C (A : Set) : Set :=
      eqb : A -> A -> bool.

    Global Instance IZ : C Z :=
      Z.eqb.

    Global Instance IString : C string :=
      String.eqb.

    Global Instance ITuple2 {A B : Set} `{C A} `{C B} : C (A * B) :=
      fun '(a1, b1) '(a2, b2) =>
        andb (eqb a1 a2) (eqb b1 b2).
  End Eq.

  Fixpoint get {K V : Set} `{Eq.C K} (dict : t K V) (key : K) : option V :=
    match dict with
    | [] => None
    | (current_key, current_value) :: dict =>
      if Eq.eqb key current_key then
        Some current_value
      else
        get dict key
    end.

  Lemma get_is_valid {K V : Set} `{Eq.C K} P_K P_V (dict : t K V) (key : K)
      (H_dict : Valid.t P_K P_V dict) :
    match get dict key with
    | None => True
    | Some value => P_V value
    end.
  Proof.
    induction dict as [|(current_key, current_value) dict IH]; cbn; trivial.
    sauto q: on.
  Qed.

  Lemma get_map_commut {K V1 V2 : Set} `{Eq.C K}
      (dict : t K V1) (key : K) (f : V1 -> V2) :
    match get dict key with
    | None => None
    | Some value => Some (f value)
    end =
    get (List.map (fun '(k, v) => (k, f v)) dict) key.
  Proof.
    induction dict as [|(current_key, current_value) dict IH]; cbn; trivial.
    hauto q: on.
  Qed.

  Definition declare {K V : Set} (dict : t K V) (key : K) (value : V) : t K V :=
    (key, value) :: dict.

  Fixpoint assign_function {K V : Set} `{Eq.C K}
      (dict : t K V) (key : K) (f : V -> V) :
      option (t K V) :=
    match dict with
    | [] => None
    | ((current_key, current_value) as entry) :: dict =>
      if Eq.eqb current_key key then
        Some ((current_key, f current_value) :: dict)
      else
        match assign_function dict key f with
        | None => None
        | Some dict => Some (entry :: dict)
        end
    end.

  Definition assign {K V : Set} `{Eq.C K} (dict : t K V) (key : K) (value : V) :
      option (t K V) :=
    assign_function dict key (fun _ => value).

  Fixpoint declare_or_assign_function {K V : Set} `{Eq.C K}
      (dict : t K V) (key : K) (f : option V -> V) :
      t K V :=
    match dict with
    | [] => [(key, f None)]
    | ((current_key, current_value) as entry) :: dict =>
      if Eq.eqb current_key key then
        (key, f (Some current_value)) :: dict
      else
        entry :: declare_or_assign_function dict key f
    end.

  Definition declare_or_assign {K V : Set} `{Eq.C K}
      (dict : t K V) (key : K) (value : V) :
      t K V :=
    declare_or_assign_function dict key (fun _ => value).

  Lemma declare_or_assign_is_valid {K V : Set} `{Eq.C K} P_K P_V
      (dict : t K V) (key : K) (value : V)
      (H_dict : Valid.t P_K P_V dict)
      (H_key : P_K key)
      (H_value : P_V value) :
    Valid.t P_K P_V (declare_or_assign dict key value).
  Proof.
    induction dict as [|(current_key, current_value) dict IH]; cbn; sauto q: on.
  Qed.

  Lemma declare_or_assign_map_commut {K V1 V2 : Set} `{Eq.C K}
      (dict : t K V1) (key : K) (value : V1) (f : V1 -> V2) :
    List.map (fun '(k, v) => (k, f v)) (declare_or_assign dict key value) =
    declare_or_assign (List.map (fun '(k, v) => (k, f v)) dict) key (f value).
  Proof.
    induction dict as [|(current_key, current_value) dict IH]; cbn; trivial.
    hauto q: on.
  Qed.
End Dict.

Module Account.
  Record t : Set := {
    balance : U256.t;
    nonce: Z;
    code : U256.t;
    (** When calling a constructor the parameters are concatenated to the code. We represent them
        here. *)
    codedata : list Z;
    storage : Storage.t;
    immutables : Dict.t U256.t U256.t;
  }.
End Account.

Module Stack.
  Definition t : Set :=
    list Locals.t.

  Definition open_scope (stack : t) : t :=
    [] :: stack.

  Definition close_scope (stack : t) : t + string :=
    match stack with
    | [] => inr "cannot close the last scope as there are none left"
    | _ :: stack => inl stack
    end.

  Fixpoint get_var (stack : t) (name : string) : U256.t + string :=
    match stack with
    | [] => inr ("variable '" ++ name ++ "' not found")%string
    | locals :: stack =>
      match Dict.get locals name with
      | None => get_var stack name
      | Some value => inl value
      end
    end.

  Definition declare_var (stack : t) (name : string) (value : U256.t) : t + string :=
    match stack with
    | [] => inr "no scope to declare the variable"
    | locals :: stack => inl (Dict.declare locals name value :: stack)
    end.

  Fixpoint declare_vars_aux (stack : t) (names : list string) (values : list U256.t) :
      option (t + string) :=
    match names, values with
    | [], [] => Some (inl stack)
    | name :: names, value :: values =>
      match declare_var stack name value with
      | inl stack => declare_vars_aux stack names values
      | inr error => Some (inr error)
      end
    | _, _ => None
    end.

  Definition declare_vars (stack : t) (names : list string) (values : list U256.t) : t + string :=
    match declare_vars_aux stack names values with
    | Some result => result
    | None =>
      inr (
        "declare: names and values have different lengths for names: " ++
        String.concat ", " names
      )%string
    end.

  Fixpoint assign_var (stack : t) (name : string) (value : U256.t) : t + string :=
    match stack with
    | [] => inr ("variable '" ++ name ++ "' not found")%string
    | locals :: stack =>
      match Dict.assign locals name value with
      | None =>
        match assign_var stack name value with
        | inl stack => inl (locals :: stack)
        | inr error => inr error
        end
      | Some locals => inl (locals :: stack)
      end
    end.

  Fixpoint assign_vars_aux (stack : t) (names : list string) (values : list U256.t) :
      option (t + string) :=
    match names, values with
    | [], [] => Some (inl stack)
    | name :: names, value :: values =>
      match assign_var stack name value with
      | inl stack => assign_vars_aux stack names values
      | inr error => Some (inr error)
      end
    | _, _ => None
    end.

  Definition assign_vars (stack : t) (names : list string) (values : list U256.t) : t + string :=
    match assign_vars_aux stack names values with
    | Some result => result
    | None =>
      inr (
        "assign: names and values have different lengths for names: " ++
        String.concat ", " names
      )%string
    end.
End Stack.

Module State.
  (** The state contains the various kinds of memory that we use in a smart contract. *)
  Record t : Set := {
    stack : Stack.t;
    memory : Memory.t;
    return_data : list Z;
    transient_storage : Storage.t;
    accounts : list (U256.t * Account.t);
    logs : list (list U256.t * list Z);
    (** This is only for debugging *)
    call_stack : CallStack.t;
  }.

  Definition init : State.t :=
    {|
      State.stack := [];
      State.memory := Memory.empty;
      State.return_data := [];
      State.transient_storage := Memory.empty;
      State.accounts := [];
      State.logs := [];
      State.call_stack := [];
    |}.
End State.

*)