From Stdlib Require Import Strings.String.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import List.
Require Import FORYU.misc.

(* [Status] of the program execution. It is shared beween YUL states
and dialects states. *)
Module Status.
  Inductive t : Type :=
  | Running : t 
  | Terminated : t
  | Reverted : t
  | Error : string -> t. 
End Status.


Module Type DIALECT.

  (* [value_t] is the type for basic values manipulated by dialect,
  e.g., 256-bits in the EVM dialect *)
  Parameter value_t : Type.

  (* A default value to be used for initializing variables *)
  Parameter default_value: value_t.

  (* [eqb v1 v2] is true iff [v1] and [v2] are equal *)
  Parameter eqb: value_t -> value_t -> bool.

  (* we require boolean equality to reflect equality. This should be
  the case for all [value_t] in this context, as there are basically
  numerical. *)
  Parameter eqb_spec : forall x y : value_t, reflect (x = y) (eqb x y).
 
  (* [is_true_value] specifies which values are [true]. Any value that
  is not [true] should be considered [false] *) 
  Parameter is_true_value: value_t -> bool.
 
  (* [opcode_t] is an inductive data type specifying the opcodes
  supported by the dialect *)
  Parameter opcode_t: Type.

  (* [dialect_state] is data type for dialect states, e.g., in EVM it
  encapsulate memory, storage, etc *)
  Parameter dialect_state_t : Type.

  (* A function to execute an opcode. It receives a dialect state, an
    opcode and a list of values, and returns a list ot output values,
    a new dialect state and the status of the execution. Should return
    an Error status if the number of arguments does not match. Adding
    it as a proposition in the smart contract's structure would
    complicate things a bit. *)
  Parameter execute_opcode: dialect_state_t -> opcode_t -> list value_t -> (list value_t * dialect_state_t * Status.t).

   (* [opcode_indep_state] specifies whether the execution of an opcode depends on the dialect state *)
  Parameter opcode_indep_state : opcode_t -> bool. 
  
  (* If [opcode_indep_state op = true], then the execution of [op] should not depend on the dialect state. *)
  Parameter opcode_indep_state_snd : forall (op: opcode_t),
    opcode_indep_state op = true -> 
    forall (s1 s2: dialect_state_t) (args: list value_t), 
    exists (res: list value_t) (status: Status.t),
    execute_opcode s1 op args = (res, s1, status) /\
    execute_opcode s2 op args = (res, s2, status).

  (* An empty dialect state, which is mainly used to testing *)
  Parameter empty_dialect_state : dialect_state_t.

  (* A function to show a value as a string, used for debugging *)
  Parameter show_value : value_t -> string.

  (* A function to show an opcode as a string, used for debugging *)
  Parameter show_opcode : opcode_t -> string.

End DIALECT.


Module DialectFacts (D : DIALECT).
    (* For rewriting [eqb x y = true] and [x = y] and vice versa *)
  Lemma eqb_eq : forall x y :D.value_t, D.eqb x y = true <-> x = y.
  Proof.
    intros x y.
    Misc.eqb_eq_from_reflect D.eqb_spec.    
  Qed.

  (* For rewriting [eqb x y <> true] and [x <> y] *)
  Lemma eqb_neq : forall x y: D.value_t, D.eqb x y <> true <-> x <> y.
  Proof.
    intros x y.
    Misc.eqb_neq_from_reflect (D.eqb_spec x y).
  Qed.

  (* For rewriting [eqb x y = false] and [x <> y] *)
  Lemma eqb_neq_false : forall x y: D.value_t, D.eqb x y = false <-> x <> y.
  Proof.
    intros x y.
    Misc.eqb_neq_from_reflect (D.eqb_spec x y).
  Qed.
  
  (* [eqb] is reflexive *)
  Lemma eqb_refl : forall x: D.value_t, D.eqb x x = true.
  Proof.
    intro x.
    Misc.eqb_eq_to_eq_refl eqb_eq.
  Qed.

  (* [eq_dec] provides [{x=y}+{x<>y}]. Usually it is not needed as
  [eqb_spec] is enough. *)  
  Definition eq_dec (x y: D.value_t): sumbool (x=y) (x<>y).
    Misc.sumbool_from_reflect (D.eqb_spec x y).
  Defined.

End DialectFacts.
