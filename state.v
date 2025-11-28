Require Export FORYU.list_functions.
Require Export FORYU.program.
 
Module VariableAssignment(D: DIALECT).

  Module YULVariableMapD := YULVariableMap(D).
  Module SimpleExprD := SimpleExpr(D).

  (* Assignment from YUL variables to dialect values *)
  Definition t := YULVariable.t -> D.value_t.
  (* Variables not initialized return the default value of the dialect *)

  Definition empty : t := fun _ => D.default_value.

  Definition assign (assignments : t) (var : YULVariable.t) (value : D.value_t) : t :=
    fun v => if YULVariable.eqb v var then value else assignments v.

  Definition get (assignments : t) (var : YULVariable.t) : D.value_t :=
    assignments var.

  (* This get recieves a list of simple expressions *)
  Definition get_se (assignments : t) (e : SimpleExprD.t) : D.value_t :=
    match e with
    | inl var => assignments var
    | inr val => val
    end.

  (* Returns a list of values for the given variables, if all variables are assigned. *)
  (* If any variable is not assigned, returns None. *)
  Definition get_all (assignments : t) (vars : list YULVariable.t) : list D.value_t :=
    List.map (fun v => get assignments v) vars.

  Definition get_all_se (assignments : t) (es : list SimpleExprD.t) : list D.value_t :=
    List.map (fun e => get_se assignments e) es.

  (* Takes a list of variables and a list of values and updates the assignment. If the list have 
     different lengths, returns None  *)
  Fixpoint assign_all (assignments : t) (vars : list YULVariable.t) (vals : list D.value_t) : option t :=
    match vars, vals with
    | nil, nil => Some assignments
    | nil, _ :: _ => None
    | _ :: _, nil => None
    | var :: rvars, val :: rvals =>
        let new_assignments := assign assignments var val in
        assign_all new_assignments rvars rvals
    (*
        match assign_all assignments rvars rvals with
        | Some new_assignments => Some (assign new_assignments var val)
        | None => None
        end
     *) 
    end.

  (* Applies a list of renamings to the assignments. Each renaming is a pair (dest, origin) where 
     dest is the variable that will take the value of origin. *)
  Fixpoint apply_renamings (assignments : t) (renamings : YULVariableMapD.t) : t :=
    match renamings with
    | nil => assignments
    | (dest, origin) :: rest =>
        apply_renamings (assign assignments dest (get_se assignments origin)) rest
    end.

End VariableAssignment.


Module StackFrame(D: DIALECT).
  (* Stack frame for a function call *)
  Module VariableAssignmentD := VariableAssignment(D).
  (* Module SmartContractD := SmartContract(D). *)
  
  
  Record t : Type := {
    function_name : FunctionName.t;
    variable_assignments : VariableAssignmentD.t;
    (* curr_block : BlockD.t; (* current block in execution, the list of instructions is consumed *) *)
    (*curr_block : SmartContractD.BlockD.t; (* current block in execution, the list of instructions is consumed *)*)
    curr_block_id: BlockID.t; (* id of the current block *)
    pc : nat; (* position of the next instructions in the curr_block *)
  }.

  Definition increase_pc (sf: t) : t :=
    {| 
      function_name := sf.(function_name);
      variable_assignments := sf.(variable_assignments);
      curr_block_id := sf.(curr_block_id);
      pc := sf.(pc) + 1;
    |}.
End StackFrame.


Module CallStack(D: DIALECT).
  (* Stack of variable assignments for the calling functions *)
  Module StackFrameD := StackFrame(D).
  Definition t := list StackFrameD.t.

  Definition empty : t := nil.
  Definition push (call_stack : t) (assignments : StackFrameD.t) : t :=
    assignments :: call_stack.
  Definition pop (call_stack : t) : t :=
    match call_stack with
    | nil => nil
    | _ :: rest => rest
    end.
End CallStack.


Module State(D: DIALECT).
  (* State of the program *)
  Module CallStackD := CallStack(D).
  Module StackFrameD := CallStackD.StackFrameD.
  Module VariableAssignmentD := StackFrameD.VariableAssignmentD.
(*  Module SmartContractD := SmartContract(D). *)
    
  Record t : Type := {
    call_stack : CallStackD.t;
    status : Status.t;
    dialect_state : D.dialect_state;
  }.

  Definition empty : t := {|
    call_stack := CallStackD.empty;
    status := Status.Running;
    dialect_state := D.empty_dialect_state;
  |}.

  (* State with with a stack frame to start block #0 of the "main" function, with pc=0 *)
  Definition initial_main : t := {|
    call_stack := ({| StackFrameD.function_name := "main"%string;
                      StackFrameD.variable_assignments := VariableAssignmentD.empty;
                      StackFrameD.curr_block_id := 0%nat;
                      StackFrameD.pc := 0%nat;
                   |} ) :: nil;
    status := Status.Running;
    dialect_state := D.empty_dialect_state;
  |}.

  Definition set_status (s: t) (new_status: Status.t) : t :=
    {| 
      call_stack := s.(call_stack);
      status := new_status;
      dialect_state := s.(dialect_state);
    |}.

End State.
