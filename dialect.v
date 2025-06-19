Module Status.
  (* Status of the program execution *)
  Inductive t : Type :=
  | Running
  | Terminated
  | Reverted.
End Status.


Module Type DIALECT.
  Parameter value_t : Type.
  Parameter opcode_t : Type.
  Parameter dialect_state : Type.
  
  Parameter is_true_value: value_t -> bool.
  Parameter is_false_value: value_t -> bool.
  Parameter equal_values: value_t -> value_t -> bool.

  Parameter execute_op_code : dialect_state -> opcode_t -> list (value_t) -> (dialect_state * Status.t).
  Parameter empty_dialect_state : dialect_state.
End DIALECT.