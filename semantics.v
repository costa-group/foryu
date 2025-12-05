Require Export FORYU.state.
Require Export FORYU.program.
Open Scope string_scope.

Module SmallStep (D: DIALECT).

  Module StateD := State(D).
  Module CallStackD := StateD.CallStackD.
  Module StackFrameD := CallStackD.StackFrameD.
  Module LocalsD := StackFrameD.LocalsD.
  Module CFGProgD := CFGProg(D).
  Module CFGFunD := CFGProgD.CFGFunD.
  Module BlockD := CFGProgD.BlockD.
  Module PhiInfoD := BlockD.PhiInfoD.
  Module InstrD := BlockD.InstrD.
  Module ExitInfoD := BlockD.ExitInfoD.
  Module SimpleExprD := ExitInfoD.SimpleExprD.
  
  Import StateD.
  Import CallStackD.
  Import StackFrameD.
  Import LocalsD.
  Import CFGProgD.
  Import CFGFunD.
  Import BlockD.
  Import PhiInfoD.
  Import InstrD.
  Import ExitInfoD.
  Import SimpleExprD.

  (* Change the status in state [s] to [Status.Error] with a message [msg] *)
  Definition error (s: StateD.t) (msg: string) :=
    StateD.set_status s (Status.Error msg).
  
  (* Generates a list of values from a list of variables/values and a stack frame *)
  Fixpoint eval_sexpr (l: list SimpleExprD.t ) (sf: StackFrameD.t) : list D.value_t :=
    match l with
    | nil => nil
    | inl var :: l' =>
        let value := get sf.(locals) var in
        value :: eval_sexpr l' sf
    | inr val :: l' =>
        val :: eval_sexpr l' sf
    end.

  (* get the next instruction to be executed, using the top stack frame of [s] *)
  Definition get_next_instr (s: StateD.t) (p: CFGProgD.t) : option InstrD.t :=
    match s.(call_stack) with
    | nil => None
    | sf :: _ => CFGProgD.get_instr p sf.(func_id) sf.(curr_bid) sf.(pc)
    end.
  

  
  (* Execute an assignment from [in_vals] to [out_vars] within the
    current stack frame [sf::rsf]. Anything else needed, apart from
    the call stack, should be taken from state [s]. The call stack in
    [s] is actually [sf::rsf] *)
  Definition execute_assignment (p: CFGProgD.t) (in_vals: list D.value_t) (out_vars: list VarID.t) (sf: StackFrameD.t) (rsf: list StackFrameD.t) (s: StateD.t): StateD.t :=
    match LocalsD.set_all sf.(locals) out_vars in_vals with
    | None => (* number of input values did not match number of output variables -- this can happen of the program is ill-formed *)
        error s "Mismatch length in output variables and input values"
    | Some locals' =>
        let sf' := {|
                    func_id := sf.(func_id);
                    locals := locals';
                    curr_bid := sf.(curr_bid);  
                    pc := sf.(pc)+1
                  |} in
        let s' := {|
                   call_stack := sf' :: rsf;
                   status := s.(status);
                   dialect_state := s.(dialect_state);
                 |} in
        s'
    end.

  (* Execute an opcode [op] using [in_vals] as input and [out_vars]
    as output, within the current stack frame [sf::rsf]. Anything else
    needed, apart from the call stack, should be taken from state
    [s]. The call stack in [s] is actually [sf::rsf] *)
  Definition execute_opcode (p: CFGProgD.t) (opcode: D.opcode_t) (in_vals: list D.value_t) (out_vars: list VarID.t) (sf: StackFrameD.t) (rsf: list StackFrameD.t) (s: StateD.t): StateD.t :=
    let '(out_vals, dialect_state', status') := D.execute_opcode s.(dialect_state) opcode in_vals in
    let s' :=  execute_assignment p out_vals out_vars sf rsf s in (* It is like execute assignment *)
    let s'' := set_dialect_state s' dialect_state' in             (* and then update dialect_state *)
    let s''' := set_status s' status' in                          (* and status *)
    s'''.

  (* Call a function [func_id] using [in_vals] as input and [out_vars]
    as output, within the current stack frame [sf::rsf]. Anything else
    needed, apart from the call stack, should be taken from state
    [s]. The call stack in [s] is actually [sf::rsf] *)
  Definition execute_func (p: CFGProgD.t) (func_id: FuncID.t) (in_vals: list D.value_t) (out_vars: list VarID.t) (sf: StackFrameD.t) (rsf: list StackFrameD.t) (s: StateD.t): StateD.t :=
    match CFGProgD.get_func p func_id with
    | None => error s "Function not found in call"
    | Some func =>
        let entry_bid := func.(entry_bid) in
        match LocalsD.set_all LocalsD.empty func.(args) in_vals with
        | None => error s "Failed to create initial variable assignment" 
        | Some locals' =>
            let sf' := {|
                        func_id := sf.(StackFrameD.func_id);
                        locals := locals';
                        curr_bid := entry_bid;
                        pc := 0
                      |} in
            let s' := {|
                       call_stack := sf' :: sf :: rsf;
                       status :=  s.(status);
                       dialect_state := s.(dialect_state);
                     |} in
            s'
        end
    end.

  (* Executes an instruction [instr] within program [p] and state [s] *)
  Definition execute_instr (instr: InstrD.t) (s: StateD.t) (p: CFGProgD.t) : StateD.t :=
    let in_sexprs := instr.(input) in
    let out_vars := instr.(output) in
    match s.(StateD.call_stack) with
    | nil => error s "No current stack frame" (* call stack empty -> error *)
    | sf :: rsf => (* call stack in not empty *)
        let in_vals := eval_sexpr in_sexprs sf in (* evaluate the parameters *)
        match instr.(op) with
        | inr ASSIGN => execute_assignment p in_vals out_vars sf rsf s
        | inl (inr opcode) => execute_opcode p opcode in_vals out_vars sf rsf s
        | inl (inl func_id) => execute_func p func_id in_vals out_vars sf rsf s
        end
    end.

  Definition apply_renamings (renamings : InBlockPhiInfo) (sf: StackFrameD.t) :=
    match renamings with
    | in_phi_info out_vars in_sexprs _ _ => 
        let out_vals := eval_sexpr in_sexprs sf in
        LocalsD.set_all sf.(locals) out_vars out_vals
    end.

  Definition handle_jump (p: CFGProgD.t) (bid: BlockID.t) (sf: StackFrameD.t) (rsf: list StackFrameD.t) (s: StateD.t): StateD.t :=
    match CFGProgD.get_block p sf.(func_id) bid with
    | None => error s  "Target block not found in the smart contract"
    | Some next_b =>
        let phi_renamings := next_b.(phi_function) sf.(curr_bid) in   (* This is the phi-function of next_b that refers to the current block *)
        match (apply_renamings phi_renamings sf) with
        | Some locals' =>                    
            let sf' := {| 
                        func_id := sf.(func_id);
                        locals := locals';
                        curr_bid := bid; 
                        pc := 0; 
                      |} in
            let s' : StateD.t := {|
                                  StateD.call_stack := sf' :: rsf;
                                  StateD.status := Status.Running;
                                  StateD.dialect_state := s.(StateD.dialect_state)
                                |} in
            s'
        | None => error s "Error while applying phi-function"
        end
    end.

  Definition handle_cond_jump (p: CFGProgD.t) (cond_var:  VarID.t) (bid_if_true bid_if_false: BlockID.t)  (sf: StackFrameD.t) (rsf: list StackFrameD.t) (s: StateD.t): StateD.t :=
    let cond_val := LocalsD.get sf.(locals) cond_var in
    if D.is_true_value cond_val
    then handle_jump p bid_if_true sf rsf s
    else handle_jump p bid_if_false sf rsf s.

  Definition handle_return (p: CFGProgD.t) (ret_sexpr: list SimpleExprD.t)  (sf: StackFrameD.t) (rsf: list StackFrameD.t) (s: StateD.t): StateD.t :=
    (* Passes return values and pops the last stack frame *)
    let ret_vals := eval_sexpr ret_sexpr sf in
    match rsf with
    | nil => error s "Missing return stack frame"
    | sf' :: rsf' =>
        match CFGProgD.get_block p sf'.(func_id) sf'.(curr_bid) with
        | None => error s "Failed to calling block"
        | Some b =>
            match List.nth_error b.(instructions) sf.(StackFrameD.pc) with
            | None => let s' := error s "Failed to find call instruction" in s'
            | Some instr =>
                let s' := StateD.set_call_stack s (sf'::rsf') in
                execute_assignment p ret_vals instr.(output) sf' rsf' s  (* It is like executing an assignment once the values are know **)
            end
        end
    end.
  
  
  Definition handle_terminate (p: CFGProgD.t) (sf: StackFrameD.t) (rsf: list StackFrameD.t) (s: StateD.t): StateD.t :=
    StateD.set_status s Status.Terminated.


  (* Handle the end of a block execution *)
  Definition handle_block_exit (s: StateD.t) (p: CFGProgD.t) : StateD.t :=
    match s.(call_stack) with
    | nil => error s "No current stack frame" (* call stack empty -> error *)
    | sf :: rsf => (* call stack in not empty *)
        match CFGProgD.get_block p sf.(func_id) sf.(curr_bid)  with
        | None => error s "Current block not found"
        | Some b =>
            match b.(exit_info) with
            | ConditionalJump cond_var bid_if_true bid_if_false =>
                handle_cond_jump p cond_var bid_if_true bid_if_false sf rsf s
            | Jump bid =>
                handle_jump p bid sf rsf s
            | ReturnBlock ret_sexprs => 
                handle_return p ret_sexprs sf rsf s
            | Terminate => 
                handle_terminate p sf rsf s
            end
        end
    end.

  
  (* Performs one execution step using program [p] and starting from state [s] *)
  Definition step (s: StateD.t) (p: CFGProgD.t) : option StateD.t :=
    match s.(StateD.status) with
    | Status.Running => 
        match get_next_instr s p with
        | None => (* No next instruction, handle the end of the block execution *)
            Some (handle_block_exit s p)
        | Some instruction => (* Execute the next instruction, which is a function or opcode call *)
            Some (execute_instr instruction s p)
        end
    | _ => None
    end.

  (* Perform [n] execution steps using program [p] and starting from state [s] *)
  Fixpoint eval (n: nat) (s: StateD.t) (p: CFGProgD.t) : option StateD.t :=
    match n with
    | 0%nat => Some s
    | S n' => match (step s p) with
              | None => None
              | Some s' => eval n' s' p
              end
    end.



End SmallStep.
