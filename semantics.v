Require Export FORYU.state.
Require Export FORYU.program.
Open Scope string_scope.


Module SmallStep (D: DIALECT).
    Module StateD := State(D).
    Module CallStackD := StateD.CallStackD.
    Module SmartContractD := SmartContract(D).
    Module StackFrameD := StateD.CallStackD.StackFrameD.
    Module BlockD := StateD.CallStackD.StackFrameD.BlockD.
    (* Module BlockD := SmartContractD.BlockD. *)
    Module VariableAssignmentD := StateD.CallStackD.StackFrameD.VariableAssignmentD.

    
    
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
    (* *************************************************************************** *)
    


    Definition handle_block_finish (s: StateD.t) (p: SmartContractD.t) : (StateD.t * Status.t) :=
        match s.(StateD.call_stack) with
        | nil => (s, Status.Error "No current stack frame") 
        | sf :: rsf => (* sf.curr_block should be [] *)
            let sf_var_assignment := sf.(StackFrameD.variable_assignments) in
            let curr_block : StackFrameD.BlockD.t := sf.(StackFrameD.curr_block) in
            let exit_info := StackFrameD.BlockD.exit_info curr_block in

            match exit_info with
            | ExitInfo.Terminated =>
                (s, Status.Terminated)

            | ExitInfo.ReturnBlock l =>
                (* Passes return values and pops the last stack frame *)
                let return_values := VariableAssignmentD.get_all sf_var_assignment l in
                match rsf with
                | nil => (* No return stack to copy values to -> Error *)
                    (s, Status.Error "Missing return stack frame")
                | prev_sf :: rsf2 => 
                    let prev_sf_var_assignment := prev_sf.(StackFrameD.variable_assignments) in
                    let vars := prev_sf.(StackFrameD.return_variables) in
                    let opt_prev_sf_var_assignment' := VariableAssignmentD.assign_all prev_sf_var_assignment vars return_values in
                    match opt_prev_sf_var_assignment' with
                    | None => (s, Status.Error "Failed to assign return values")
                    | Some prev_sf_var_assignment' =>
                        let prev_sf' := {| 
                            StackFrameD.function_name := prev_sf.(StackFrameD.function_name);
                            StackFrameD.variable_assignments := prev_sf_var_assignment';
                            StackFrameD.curr_block := prev_sf.(StackFrameD.curr_block);
                            StackFrameD.return_variables := prev_sf.(StackFrameD.return_variables) 
                        |} in
                        let new_state : StateD.t := {|
                                StateD.call_stack := prev_sf' :: rsf2;
                                StateD.status := s.(StateD.status); (* Keep the previous status *)
                                StateD.dialect_state := s.(StateD.dialect_state);
                        |} in
                        (s, Status.Running)
                    end
                end

            | ExitInfo.Jump target_block =>
                let fname := sf.(StackFrameD.function_name) in
                let opt_target_block := SmartContractD.get_block p fname target_block in
                match opt_target_block with
                | None => (s, Status.Error "Jump to non-existing block")
                | Some target_block' =>
                    (* Update the current block to the target block and keep the rest of the stack frame *)
                    let sf' := {| 
                        StackFrameD.function_name := sf.(StackFrameD.function_name);
                        StackFrameD.variable_assignments := sf.(StackFrameD.variable_assignments);
                        StackFrameD.curr_block := cast_block target_block'; (* Cast between different module alias *)
                        StackFrameD.return_variables := sf.(StackFrameD.return_variables) 
                    |} in
                    let call_stack' := sf' :: rsf in
                    let s' : StateD.t := {|
                        StateD.call_stack := call_stack';
                        StateD.status := s.(StateD.status); (* Keep the previous status *)
                        StateD.dialect_state := s.(StateD.dialect_state);
                    |} in
                    (s', Status.Running)
                end

            | _ => (s, Status.Error "Not implemented")
            end
        end.

    Definition step (s: StateD.t) (p: SmartContractD.t) : (StateD.t * Status.t):=
        (s, Status.Running).

End SmallStep.