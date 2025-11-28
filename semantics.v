Require Export FORYU.state.
Require Export FORYU.program.
Open Scope string_scope.


(* 
** TODO: handle phi-function information **
- both in handle_block_finish and execute call (define function part)
- Create function to create/adapt variable assignment with phi-info
*)


Module SmallStep (D: DIALECT).
    Module StateD := State(D).
    Module CallStackD := StateD.CallStackD.
    Module SmartContractD := SmartContract(D).
    Module BlockD := SmartContractD.BlockD.
    Module StackFrameD := StateD.CallStackD.StackFrameD.
    (* Module BlockD := StateD.CallStackD.StackFrameD.BlockD. *)
    (* Module BlockD := SmartContractD.BlockD. *)
    Module VariableAssignmentD := StateD.CallStackD.StackFrameD.VariableAssignmentD.
    Module ExitInfoD := BlockD.ExitInfoD.
    Module SimpleExprD := ExitInfoD.SimpleExprD.
    
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
                | ExitInfoD.Terminated => let s' := StateD.set_status s (Status.Terminated) in
                                         s' (* Should we clear the stack frame? *)


                | ExitInfoD.ReturnBlock l =>
                    (* Passes return values and pops the last stack frame *)
                    let return_values := VariableAssignmentD.get_all_se sf_var_assignment l in
                    match rsf with
                    | nil => (* No return stack to copy values to -> Error *)
                        let s' := StateD.set_status s (Status.Error "Missing return stack frame") in s'
                    | prev_sf :: rsf2 =>
                        match SmartContractD.get_block p prev_sf.(StackFrameD.function_name) prev_sf.(StackFrameD.curr_block_id) with
                        | None => let s' := StateD.set_status s (Status.Error "Failed to calling block") in s'
                        | Some b =>
                            match List.nth_error b.(BlockD.instructions) prev_sf.(StackFrameD.pc) with
                            | None => let s' := StateD.set_status s (Status.Error "Failed to find call instruction") in s'
                            | Some instr =>
                                let prev_sf_var_assignment := prev_sf.(StackFrameD.variable_assignments) in
                                let vars := instr.(SmartContractD.BlockD.InstructionD.output) in
                                let opt_prev_sf_var_assignment' := VariableAssignmentD.assign_all prev_sf_var_assignment vars return_values in
                                match opt_prev_sf_var_assignment' with
                                | None => let s' := StateD.set_status s (Status.Error "Failed to assign return values") in
                                          s'
                                | Some prev_sf_var_assignment' =>
                                    let prev_sf' := {| 
                                                     StackFrameD.function_name := prev_sf.(StackFrameD.function_name);
                                                     StackFrameD.variable_assignments := prev_sf_var_assignment';
                                                     StackFrameD.curr_block_id := prev_sf.(StackFrameD.curr_block_id);
                                                     StackFrameD.pc := prev_sf.(StackFrameD.pc)+1; (* Increment the previous pc *)
                                                   |} in
                                    let s' : StateD.t := {|
                                                          StateD.call_stack := prev_sf' :: rsf2;
                                                          (* StateD.status := s.(StateD.status); (* Keep the previous status *) *)
                                                          StateD.status := Status.Running;
                                                          StateD.dialect_state := s.(StateD.dialect_state); |} in
                                    s'
                                end
                            end
                        end
                    end


                | ExitInfoD.Jump target_block =>
                    (* Jump to the target block, resetting the program counter *)
                    let var_assignments := sf.(StackFrameD.variable_assignments) in
                    match SmartContractD.get_block p function_name target_block with
                    | None => let s' := StateD.set_status s (Status.Error "Target block not found in the smart contract") in
                              s'

                    | Some target_block_data =>
                        let phi_function := SmartContractD.BlockD.phi_function target_block_data in
                        let phi_renamings := phi_function curr_block_id in
                        let var_assignments' := VariableAssignmentD.apply_renamings var_assignments phi_renamings in  
                    
                        let sf' := {| 
                            StackFrameD.function_name := function_name;
                            StackFrameD.variable_assignments := var_assignments';
                            StackFrameD.curr_block_id := target_block; 
                            StackFrameD.pc := 0; (* Reset the program counter to the start of the target block *)
                                  |} in
                        let call_stack' := sf' :: rsf in
                        let s' : StateD.t := {|
                            StateD.call_stack := call_stack';
                            StateD.status := Status.Running;
                            StateD.dialect_state := s.(StateD.dialect_state) |} in
                        s'
                    end 


                | ExitInfoD.ConditionalJump cond_var target_if_true target_if_false =>
                    let cond_val := VariableAssignmentD.get sf.(StackFrameD.variable_assignments) cond_var in
                    let target_block := if D.is_true_value cond_val then target_if_true else target_if_false in
                    let var_assignments := sf.(StackFrameD.variable_assignments) in
                    match SmartContractD.get_block p function_name target_block with
                    | None => let s' := StateD.set_status s (Status.Error "Target block not found in the smart contract") in
                              s'

                    | Some target_block_data =>
                        let phi_function := SmartContractD.BlockD.phi_function target_block_data in
                        let phi_renamings := phi_function curr_block_id in
                        let var_assignments' := VariableAssignmentD.apply_renamings var_assignments phi_renamings in  
                    
                        let sf' := {| 
                            StackFrameD.function_name := function_name;
                            StackFrameD.variable_assignments := var_assignments';
                            StackFrameD.curr_block_id := target_block; 
                            StackFrameD.pc := 0; (* Reset the program counter to the start of the target block *)
                                  |} in
                        let call_stack' := sf' :: rsf in
                        let s' : StateD.t := {|
                            StateD.call_stack := call_stack';
                            StateD.status := Status.Running;
                            StateD.dialect_state := s.(StateD.dialect_state) |} in
                        s'
                    end
                end
            end
        end.


    (* Generates a list of values from a list of variables/values and a stack frame *)
    Fixpoint eval_input (input: list SimpleExprD.t ) (sf: StackFrameD.t) : list D.value_t :=
        match input with
        | nil => nil
        | inl var :: rest =>
            let value := VariableAssignmentD.get sf.(StackFrameD.variable_assignments) var in
            value :: eval_input rest sf
        | inr val :: rest =>
            val :: eval_input rest sf
        end.


    (* Executes a call instruction *)
    Definition execute_instr (instr: SmartContractD.BlockD.InstructionD.t) (s: StateD.t) (p: SmartContractD.t) : StateD.t :=
        let input := instr.(SmartContractD.BlockD.InstructionD.input) in
        let output := instr.(SmartContractD.BlockD.InstructionD.output) in       
        match s.(StateD.call_stack) with
            | nil => let s' := StateD.set_status s (Status.Error "No current stack frame") in
                     s'
            | sf :: rsf => 
                let input_values := eval_input input sf in
        
                match instr.(SmartContractD.BlockD.InstructionD.op) with

                (* Execute an assignment *)
                | inr ASSIGN => 
                    let variable_assignments := sf.(StackFrameD.variable_assignments) in
                    let opt_var_assignments' := VariableAssignmentD.assign_all variable_assignments output input_values in
                    match opt_var_assignments' with
                    | None => let s' := StateD.set_status s (Status.Error "Mismatch length in output variables and values in assignment instruction") in
                              s'
                    | Some var_assignments' =>
                        let sf' := {|
                                    StackFrameD.function_name := sf.(StackFrameD.function_name);
                                    StackFrameD.variable_assignments := var_assignments';
                                    StackFrameD.curr_block_id := sf.(StackFrameD.curr_block_id);  
                                    StackFrameD.pc := sf.(StackFrameD.pc) + 1; (* Increment the program counter *)
                                  |} in
                        let call_stack' := sf' :: rsf in
                        let s' : StateD.t := {|
                                              StateD.call_stack := call_stack';
                                              StateD.status := s.(StateD.status);
                                              StateD.dialect_state := s.(StateD.dialect_state);
                                            |} in
                        s'
                    end

                (* Execute a call *)                                  
                | inl call_instr =>
                    match call_instr with
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
                            (* TODO: CHECK WITH SAMIR: The entry block of a function cannot have phi information to rename variables *)
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
                                             |} in 
                                (* let sf' := StackFrameD.increase_pc sf in *)
                                let s' : StateD.t := {|
                                                      StateD.call_stack := new_sf :: sf :: rsf;
                                                      StateD.status := s.(StateD.status);
                                                      StateD.dialect_state := s.(StateD.dialect_state);
                                                    |} in
                                s'
                            end
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
                execute_instr instruction s p
            end
        | _ => s (* If the status is not running, return the state as is *)
        end.


    Fixpoint eval (steps: nat) (s: StateD.t) (p: SmartContractD.t) : StateD.t :=
        match steps with
        | 0%nat => s
        | S n => eval n (step s p) p
        end.

End SmallStep.
