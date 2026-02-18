Require Export FORYU.program.
Require Export FORYU.semantics.
Require Export FORYU.liveness.
Require Export FORYU.evm_dialect.
Require Export FORYU.liveness.
Require Import NArith.
Require Import Coq.ZArith.ZArith.
Require Import Arith.
Import ListNotations.

Module Checker.
    (* Module to load all the relevant datatypes and export them into OCaml *)

    Module EVMLiveness := Liveness(EVMDialect).
    Module EVMSmallStep := EVMLiveness.SmallStepD.
    Module EVMCFGProg := EVMSmallStep.CFGProgD.
    Module EVMCFGFun := EVMCFGProg.CFGFunD.
    Module EVMBlock := EVMCFGFun.BlockD.
    Module EVMInstr := EVMBlock.InstrD.
    Module EVMState := EVMSmallStep.StateD.
    Module EVMPhiInfo := EVMBlock.PhiInfoD.
    Module ExitInfo := EVMBlock.ExitInfoD.


    Definition exit1 : ExitInfo.t := ExitInfo.Terminate.
    Definition phi1 := EVMPhiInfo.empty. 

    Lemma lnodup : NoDup [1%N].
    Proof.
        apply NoDup_cons.
        - auto.
        - apply NoDup_nil.
    Qed.

    Definition i2 : EVMInstr.t := (* v1 := ISZERO v3 *)
        {|  EVMInstr.input := [inl 3%N];
            EVMInstr.output := [1%N];
            EVMInstr.op := inl (inr EVM_opcode.ISZERO);
            EVMInstr.H_nodup := lnodup |}.

    Definition b1 : EVMBlock.t := 
        {| EVMBlock.bid := 1%N;
           EVMBlock.instructions := [i2];
           EVMBlock.exit_info := exit1;
           EVMBlock.phi_function := phi1;
            |}.

    Definition fun1 : EVMCFGFun.t := 
        {| EVMCFGFun.name := "myfunc";
           EVMCFGFun.args := [1%N];
           EVMCFGFun.blocks := [b1];
           EVMCFGFun.entry_bid := 1%N;
           EVMCFGFun.H_nodup := lnodup;
        |}.

    Definition prog : EVMCFGProg.t := 
        {| EVMCFGProg.name := "Program";
           EVMCFGProg.functions := [fun1];
           EVMCFGProg.main := "myfunc";
        |}.

    Definition liveness_info : EVMLiveness.prog_live_info_t := fun _ => None.
        
    Definition apply_checker := 
        EVMLiveness.check_program prog liveness_info.



    (*
    Definition string_of_nat (n : nat) : string := 
        "ojete".
    
    Definition string_of_N (n : N) : string := 
        "piticli".

    Definition string_of_list {A : Type} (f : A -> string) (sep : string) (l : list A) : string :=
        String.concat sep (List.map f l).

    Definition string_of_instr (instr : EVMInstr.t) : string :=
        "  instr: input=[" ++ string_of_list string_of_N "," instr.(EVMInstr.input) ++ 
        "] output=[" ++ string_of_list string_of_N "," instr.(EVMInstr.output) ++ "]".

    Definition string_of_block (block : EVMBlock.t) : string :=
        "Block " ++ string_of_N block.(EVMBlock.bid) ++ ":" ++ String.newline ++
        string_of_list string_of_instr String.newline block.(EVMBlock.instructions) ++ String.newline ++
        "  exit: " ++ (match block.(EVMBlock.exit_info) with
                       | ExitInfo.Terminate => "Terminate"
                       | ExitInfo.Jump _ => "Jump"
                       | ExitInfo.ConditionalJump _ _ _ => "ConditionalJump"
                       | ExitInfo.ReturnBlock _ => "Return"
                       end) ++ String.newline.

    Definition string_of_fun (fun_def : EVMCFGFun.t) : string :=
        "Function: " ++ fun_def.(EVMCFGFun.name) ++ String.newline ++
        "  args: [" ++ string_of_list string_of_N "," fun_def.(EVMCFGFun.args) ++ "]" ++ String.newline ++
        "  entry: " ++ string_of_N fun_def.(EVMCFGFun.entry_bid) ++ String.newline ++
        string_of_list string_of_block String.newline fun_def.(EVMCFGFun.blocks) ++ String.newline.

    Definition pretty_print_prog (p : EVMCFGProg.t) : string :=
        "Program: " ++ p.(EVMCFGProg.name) ++ String.newline ++
        "Main: " ++ p.(EVMCFGProg.main) ++ String.newline ++ String.newline ++
        string_of_list string_of_fun String.newline p.(EVMCFGProg.functions).     
    *)
End Checker.