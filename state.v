Require Export FORYU.list_functions.
Require Export FORYU.program.

Module Locals(D: DIALECT).

  Module SimpleExprD := SimpleExpr(D).

  (* Mapping from YUL local variables to dialect values -- we have
  infinite number of registers*)
  Definition t := VarID.t -> D.value_t.

  (* VarIDiables not initialized return the default value of the dialect
  *)
  Definition empty : t := fun _ => D.default_value.

  (* sets the value of [var] to [value] in [locals] *)
  Definition set (locals : t) (var : VarID.t) (value : D.value_t) : t :=
    fun v => if VarID.eqb v var then value else locals v.

  (* Takes a list of variables and a list of values and updates sets
     all of them. If the lists have different lengths, returns None *)
  Fixpoint set_all (locals : t) (vars : list VarID.t) (vals : list D.value_t) : option t :=
    match vars, vals with
    | nil, nil => Some locals
    | nil, _ :: _ => None
    | _ :: _, nil => None
    | var :: rvars, val :: rvals =>
        let locals' := set locals var val in
        set_all locals' rvars rvals
    end.

  (* returns the value of [var] in [locals] *)
  Definition get (locals : t) (var : VarID.t) : D.value_t :=
    locals var.

  (* Returns a list of values for the given variables *)
  Definition get_all (locals : t) (vars : list VarID.t) : list D.value_t :=
    List.map (fun v => get locals v) vars.


End Locals.


Module StackFrame(D: DIALECT).
  (* Stack frame for a function call *)
  Module LocalsD := Locals(D).
  
  Record t : Type := {
      func_id : FuncID.t;
      locals : LocalsD.t;
      curr_bid: BlockID.t; (* id of the current block *)
      pc : nat; (* position of the next instructions in the current block. We keep using nat becuase there are many code/theorems we need that do not exists for N. Idieally we shoukd use N for efficiency in the different analysis. *)
    }.
 
End StackFrame.



Module CallStack(D: DIALECT).
  (* Stack of variable assignments for the calling functions *)
  Module StackFrameD := StackFrame(D).

  Definition t := list StackFrameD.t.

  Definition empty : t := nil.
End CallStack.


Module State(D: DIALECT).
  (* State of the program *)
  Module CallStackD := CallStack(D).
  Module StackFrameD := CallStackD.StackFrameD.
  Module LocalsD := StackFrameD.LocalsD.
    
  Record t : Type := {
    call_stack : CallStackD.t;
    status : Status.t;
    dialect_state : D.dialect_state_t;
  }.

  Definition set_status (s: t) (status: Status.t) : t :=
    {| 
      call_stack := s.(call_stack);
      status := status;
      dialect_state := s.(dialect_state);
    |}.

  Definition set_dialect_state (s: t) (dialect_state: D.dialect_state_t) : t :=
    {| 
      call_stack := s.(call_stack);
      status := s.(status);
      dialect_state := dialect_state;
    |}.

  Definition set_call_stack (s: t) (call_stack': CallStackD.t) : t :=
    {| 
      call_stack := call_stack';
      status := s.(status);
      dialect_state := s.(dialect_state)
    |}.

End State.

