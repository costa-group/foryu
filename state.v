Require Export FORYU.program.


Module VariableAssignment(D: DIALECT).
  (* Assignment from YUL variables to dialect values *)
  Definition t := list (YULVariable.t * D.value_t).

  Definition empty : t := nil.
  Definition assign (assignments : t) (var : YULVariable.t) (value : D.value_t) : t :=
    (var, value) :: assignments.
  Definition get (assignments : t) (var : YULVariable.t) : option D.value_t :=
    match List.find (fun '(v,_) => YULVariable.eqb v var) assignments with
    | None => None
    | Some (_, value) => Some value
    end.
End VariableAssignment.


Module CallStack(D: DIALECT).
  (* Stack of variable assignments for the calling functions *)
  Module VariableAssignmentD := VariableAssignment(D).
  Definition t := list VariableAssignmentD.t.

  Definition empty : t := nil.
  Definition push (call_stack : t) (assignments : VariableAssignmentD.t) : t :=
    assignments :: call_stack.
  Definition pop (call_stack : t) : t :=
    match call_stack with
    | nil => nil
    | _ :: rest => rest
    end.
End CallStack.


Module State(D: DIALECT).
  (* State of the program *)
  Module VariableAssignmentD := VariableAssignment(D).
  Module CallStackD := CallStack(D).
    
  Record t : Type := {
    variable_assignments : VariableAssignmentD.t;
    call_stack : CallStackD.t;
    status : Status.t;
    dialect_state : D.dialect_state;
  }.

  Definition empty : t := {|
    variable_assignments := VariableAssignmentD.empty;
    call_stack := CallStackD.empty;
    status := Status.Running;
    dialect_state := D.empty_dialect_state;
  |}.
End State.