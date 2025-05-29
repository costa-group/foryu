Require Export Coq.ZArith.ZArith.
Global Open Scope Z_scope.


Module U256.
  Definition t := Z.

  Module Valid.
    Definition t (value : U256.t) : Prop :=
      0 <= value < 2 ^ 256.
  End Valid.

  Definition of_bool (b : bool) : U256.t :=
    if b then 1 else 0.
End U256.


Module EVM_opcode.
  Inductive t :=
    | ADD
    | MUL
    | SUB
    | DIV
    | SDIV
    | MOD
    | SMOD
    | ADDMOD
    | MULMOD
    | EXP
    | SIGNEXTEND
    | LT
    | GT
    | SLT
    | SGT
    | EQ
    | ISZERO
    | AND
    | OR
    | XOR
    | NOT
    | BYTE
    | SHL
    | SHR
    | SAR
    | ADDRESS
    | BALANCE
    | ORIGIN
    | CALLER
    | CALLVALUE
    | CALLDATALOAD
    | CALLDATASIZE
    | CODESIZE
    | GASPRICE
    | EXTCODESIZE
    | RETURNDATASIZE
    | EXTCODEHASH
    | BLOCKHASH
    | COINBASE
    | TIMESTAMP
    | NUMBER
    | DIFFICULTY
    | GASLIMIT
    | CHAINID
    | SELFBALANCE
    | BASEFEE
    | GAS
    | JUMPI. (* This is implemented with a different semantics!! It does not really jump. We need it to handle blocks that end with JUMPI but their corresponding optimized one ends with JMP *)


    Definition eqb (a b: EVM_opcode.t) : bool :=
        match a,b with
        | ADD,ADD => true
        | MUL,MUL => true
        | SUB,SUB => true
        | DIV,DIV => true
        | SDIV,SDIV => true
        | MOD,MOD => true
        | SMOD,SMOD => true
        | ADDMOD,ADDMOD => true
        | MULMOD,MULMOD => true
        | EXP,EXP => true
        | SIGNEXTEND,SIGNEXTEND => true
        | LT,LT => true
        | GT,GT => true
        | SLT,SLT => true
        | SGT,SGT => true
        | EQ,EQ => true
        | ISZERO,ISZERO => true
        | AND,AND => true
        | OR,OR => true
        | XOR,XOR => true
        | NOT,NOT => true
        | BYTE,BYTE => true
        | SHL,SHL => true
        | SHR,SHR => true
        | SAR,SAR => true
        | ADDRESS,ADDRESS => true
        | BALANCE,BALANCE => true
        | ORIGIN,ORIGIN => true
        | CALLER,CALLER => true
        | CALLVALUE,CALLVALUE => true
        | CALLDATALOAD,CALLDATALOAD => true
        | CALLDATASIZE,CALLDATASIZE => true
        | GASPRICE,GASPRICE => true
        | EXTCODESIZE,EXTCODESIZE => true
        | RETURNDATASIZE,RETURNDATASIZE => true
        | EXTCODEHASH,EXTCODEHASH => true
        | BLOCKHASH,BLOCKHASH => true
        | COINBASE,COINBASE => true
        | TIMESTAMP,TIMESTAMP => true
        | NUMBER,NUMBER => true
        | DIFFICULTY,DIFFICULTY => true
        | GASLIMIT,GASLIMIT => true
        | CHAINID,CHAINID => true
        | SELFBALANCE,SELFBALANCE => true
        | BASEFEE,BASEFEE => true
        | CODESIZE,CODESIZE => true
        | GAS, GAS => true
        | JUMPI, JUMPI => true
        | _,_ => false
        end.

    (* Lemma eqb_stack_op_instr_eq:
    forall (a b: stack_op_instr),
        eqb_stack_op_instr a b = true -> a = b.
    Proof.
    intros a b H.
    unfold eqb_stack_op_instr in H. 
    destruct a; destruct b; try reflexivity || discriminate.
    Qed.

    Definition stack_op_eq_dec : forall (a b : stack_op_instr), { a = b } + { a <> b }.
    Proof.
    decide equality.
    Defined.
    *)
End EVM_opcode.
