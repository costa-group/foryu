Require Export FORYU.state.
Require Export FORYU.program.
Open Scope string_scope.


Module SmallStep (D: DIALECT).
    Module StateD := State(D).
    Module CallStackD := StateD.CallStackD.
    Module SmartContractD := SmartContract(D).
    Module StackFrameD := StateD.CallStackD.StackFrameD.
    (* Module BlockD := StateD.CallStackD.StackFrameD.BlockD. *)
    (* Module BlockD := SmartContractD.BlockD. *)
    Module VariableAssignmentD := StateD.CallStackD.StackFrameD.VariableAssignmentD.

    
    (*
    (* SmartContractD.BlockD.InstructionD and BlockD.InstructionD are considered different modules *)
    (* The solution is to create a value of type BlockD.InstructionD.t from a value of type
       SmartContractD.BlockD.InstructionD.t. It requires nested castings until reaching base modules *)
    Definition cast_instruction (i: SmartContractD.BlockD.InstructionD.t) :
            BlockD.InstructionD.t :=
        {|
            BlockD.InstructionD.input := SmartContractD.BlockD.InstructionD.input i;
            BlockD.InstructionD.output := SmartContractD.BlockD.InstructionD.output i;
            BlockD.InstructionD.op := SmartContractD.BlockD.InstructionD.op i;
        |}.

    Fixpoint cast_instructions (l: list SmartContractD.BlockD.InstructionD.t) :
            list BlockD.InstructionD.t :=
        match l with
        | nil => nil
        | i :: rest => 
            (cast_instruction i) :: cast_instructions rest
        end.
    
    Definition cast_block (b : SmartContractD.BlockD.t) : StackFrameD.BlockD.t := {| 
        StackFrameD.BlockD.bid := SmartContractD.BlockD.bid b;
        StackFrameD.BlockD.phi_function := SmartContractD.BlockD.phi_function b;
        StackFrameD.BlockD.exit_info := SmartContractD.BlockD.exit_info b;
        StackFrameD.BlockD.instructions := cast_instructions (SmartContractD.BlockD.instructions b);
    |}.

    (* problem: this is ill-typed because b1 and b2 have different types (of course!) *)
    (* 
    Lemma eq_cast: forall (b1 : SmartContractD.BlockD.t) (b2 : StackFrameD.BlockD.t),
        cast_block b1 = b2 -> b1 = b2.
    *)
    *)
    (* *************************************************************************** *)
    

    Definition get_next_instruction (s: StateD.t) (p: SmartContractD.t) : option SmartContractD.BlockD.InstructionD.t :=
        match s.(StateD.call_stack) with
        | nil => None
        | sf :: _ =>
            let function_name := sf.(StackFrameD.function_name) in
            let curr_block_id : BlockID.t := sf.(StackFrameD.curr_block_id) in
            let pc := sf.(StackFrameD.pc) in
            SmartContractD.get_instruction p function_name curr_block_id pc
        end.

    (*
    Definition create_init_var_assignment (p: SmartContractD.t) (fname: FunctionName.t) 
        (input: list D.value_t) : option VariableAssignmentD.t :=
    match SmartContractD.get_function p fname with
    | Some func =>
        CallStackD.StackFrameD.VariableAssignmentD.assign_all 
            CallStackD.StackFrameD.VariableAssignmentD.empty 
            func.(SmartContractD.FunctionD.arguments) input
    | None => None
    end.
    *)

    (* Handle the end of a block execution *)
    Definition handle_block_finish (s: StateD.t) (p: SmartContractD.t) : StateD.t :=
        match s.(StateD.call_stack) with
        | nil => let s' := StateD.set_status s (Status.Error "No current stack frame") in
                 s' 
        | sf :: rsf => (* sf.pc should be > sf.curr_block length *)
            let function_name := sf.(StackFrameD.function_name) in
            let sf_var_assignment := sf.(StackFrameD.variable_assignments) in
            let curr_block_id : BlockID.t := sf.(StackFrameD.curr_block_id) in
            let opt_curr_block : option SmartContractD.BlockD.t := SmartContractD.get_block p function_name curr_block_id in
            match opt_curr_block with
            | None => let s' := StateD.set_status s (Status.Error "Current block not found in the smart contract") in
                      s'
            | Some curr_block =>
                let exit_info := SmartContractD.BlockD.exit_info curr_block in


                match exit_info with
                | ExitInfo.Terminated => let s' := StateD.set_status s (Status.Terminated) in
                                         s'


                | ExitInfo.ReturnBlock l =>
                    (* Passes return values and pops the last stack frame *)
                    let return_values := VariableAssignmentD.get_all sf_var_assignment l in
                    match rsf with
                    | nil => (* No return stack to copy values to -> Error *)
                        let s' := StateD.set_status s (Status.Error "Missing return stack frame") in
                        s'
                    | prev_sf :: rsf2 => 
                        let prev_sf_var_assignment := prev_sf.(StackFrameD.variable_assignments) in
                        let vars := prev_sf.(StackFrameD.return_variables) in
                        let opt_prev_sf_var_assignment' := VariableAssignmentD.assign_all prev_sf_var_assignment vars return_values in
                        match opt_prev_sf_var_assignment' with
                        | None => let s' := StateD.set_status s (Status.Error "Failed to assign return values") in
                                  s'
                        | Some prev_sf_var_assignment' =>
                            let prev_sf' := {| 
                                StackFrameD.function_name := prev_sf.(StackFrameD.function_name);
                                StackFrameD.variable_assignments := prev_sf_var_assignment';
                                StackFrameD.curr_block_id := prev_sf.(StackFrameD.curr_block_id);
                                StackFrameD.pc := prev_sf.(StackFrameD.pc); (* Keep the previous program counter *)
                                StackFrameD.return_variables := prev_sf.(StackFrameD.return_variables) 
                            |} in
                            let s' : StateD.t := {|
                                    StateD.call_stack := prev_sf' :: rsf2;
                                    (* StateD.status := s.(StateD.status); (* Keep the previous status *) *)
                                    StateD.status := Status.Running;
                                    StateD.dialect_state := s.(StateD.dialect_state); |} in
                            s'
                        end
                    end


                | ExitInfo.Jump target_block =>
                    let sf' := {| 
                        StackFrameD.function_name := function_name;
                        StackFrameD.variable_assignments := sf.(StackFrameD.variable_assignments);
                        StackFrameD.curr_block_id := target_block; 
                        StackFrameD.pc := 0; (* Reset the program counter to the start of the target block *)
                        StackFrameD.return_variables := sf.(StackFrameD.return_variables) |} in
                    let call_stack' := sf' :: rsf in
                    let s' : StateD.t := {|
                        StateD.call_stack := call_stack';
                        (* StateD.status := s.(StateD.status); (* Keep the previous status *) *)
                        StateD.status := Status.Running;
                        StateD.dialect_state := s.(StateD.dialect_state) |} in
                    s'


                | ExitInfo.ConditionalJump cond_var target_if_true target_if_false =>
                    let cond_val := VariableAssignmentD.get sf.(StackFrameD.variable_assignments) cond_var in
                    let target_block := if D.is_true_value cond_val then target_if_true else target_if_false in
                    let sf' := {| 
                        StackFrameD.function_name := function_name;
                        StackFrameD.variable_assignments := sf.(StackFrameD.variable_assignments);
                        StackFrameD.curr_block_id := target_block; 
                        StackFrameD.pc := 0; (* Reset the program counter to the start of the target block *)
                        StackFrameD.return_variables := sf.(StackFrameD.return_variables) |} in
                    let call_stack' := sf' :: rsf in
                    let s' : StateD.t := {|
                        StateD.call_stack := call_stack';
                        (* StateD.status := s.(StateD.status); (* Keep the previous status *) *)
                        StateD.status := Status.Running;
                        StateD.dialect_state := s.(StateD.dialect_state) |} in
                    s'
                end
            end
        end.

    (* Generates a list of values from a list of variables/values and a stack frame *)
    Fixpoint eval_input (input: list (YULVariable.t + D.value_t)) (sf: StackFrameD.t) : list D.value_t :=
        match input with
        | nil => nil
        | inl var :: rest =>
            let value := VariableAssignmentD.get sf.(StackFrameD.variable_assignments) var in
            value :: eval_input rest sf
        | inr val :: rest =>
            val :: eval_input rest sf
        end.


    (* Executes a call instruction *)
    Definition execute_call (instr: SmartContractD.BlockD.InstructionD.t) (s: StateD.t) (p: SmartContractD.t) : StateD.t :=
        let input := instr.(SmartContractD.BlockD.InstructionD.input) in
        let output := instr.(SmartContractD.BlockD.InstructionD.output) in       
        match s.(StateD.call_stack) with
            | nil => let s' := StateD.set_status s (Status.Error "No current stack frame") in
                     s'
            | sf :: rsf => 
                let input_values := eval_input input sf in
        
                match instr.(SmartContractD.BlockD.InstructionD.op) with
                | inr opcode =>
                    (* Execute an opcode *)
                    
                    let '(output_values, new_dialect_state, status) :=
                        D.execute_op_code s.(StateD.dialect_state) opcode input_values in
                    let variable_assignments := sf.(StackFrameD.variable_assignments) in
                    let opt_var_assignments' := VariableAssignmentD.assign_all variable_assignments output output_values in
                    match opt_var_assignments' with
                    | None => let s' := StateD.set_status s (Status.Error "Mismatch length in output variables and values in opcode execution") in
                        s'
                    | Some var_assignments' =>
                        let sf' := {|
                            StackFrameD.function_name := sf.(StackFrameD.function_name);
                            StackFrameD.variable_assignments := var_assignments';
                            StackFrameD.curr_block_id := sf.(StackFrameD.curr_block_id);  
                            StackFrameD.pc := sf.(StackFrameD.pc) + 1; (* Increment the program counter *)
                            StackFrameD.return_variables := sf.(StackFrameD.return_variables)
                        |} in
                        let call_stack' := sf' :: rsf in
                        let s' : StateD.t := {|
                            StateD.call_stack := call_stack';
                            StateD.status := status;
                            StateD.dialect_state := new_dialect_state;
                        |} in
                        s'
                    end


                | inl fname =>
                    (* Execute a function call *)
                    match SmartContractD.get_function p fname with
                    | None => 
                        let s' := StateD.set_status s (Status.Error "Function not found in call") in
                        s'
                    | Some func =>
                        let first_block_id := func.(SmartContractD.FunctionD.entry_block_id) in
                        let opt_var_assignments := 
                            CallStackD.StackFrameD.VariableAssignmentD.assign_all 
                                CallStackD.StackFrameD.VariableAssignmentD.empty 
                                func.(SmartContractD.FunctionD.arguments) input_values in
                        match opt_var_assignments with
                        | None => let s' := StateD.set_status s (Status.Error "Failed to create initial variable assignment") in
                            s'
                        | Some var_assignments =>
                            let new_sf := {|
                                StackFrameD.function_name := fname;
                                StackFrameD.variable_assignments := var_assignments;
                                StackFrameD.curr_block_id := first_block_id; 
                                StackFrameD.pc := 0; (* Start at the first instruction of the block *)
                                StackFrameD.return_variables := output (* The output variables will receive the return values *)
                            |} in 
                            let sf' := StackFrameD.increase_pc sf in
                            let s' : StateD.t := {|
                                StateD.call_stack := new_sf :: sf' :: rsf;
                                StateD.status := s.(StateD.status);
                                StateD.dialect_state := s.(StateD.dialect_state);
                            |} in
                            s'
                        end
                    end
                end
        end.

    
    (* Performs one step of execution *)
    Definition step (s: StateD.t) (p: SmartContractD.t) : StateD.t :=
        match s.(StateD.status) with
        | Status.Running => 
            match get_next_instruction s p with
            | None =>
                (* No next instruction, handle the end of the block execution *)
                handle_block_finish s p
            | Some instruction =>
                (* Execute the next instruction, which is a function or opcode call *)
                execute_call instruction s p
            end
        | _ => s (* If the status is not running, return the state as is *)
        end.

    Fixpoint eval (steps: nat) (s: StateD.t) (p: SmartContractD.t) : StateD.t :=
        match steps with
        | 0%nat => s
        | S n => 
            match s.(StateD.status) with
            | Status.Running => let s' := step s p in eval n s' p
            | _ => s (* If the status is not running, return the state as is *)
            end
        end.

End SmallStep.