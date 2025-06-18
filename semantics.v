Require Export FORYU.state.
Require Export FORYU.program.


Module SmallStep (D: DIALECT).
    Module StateD := State(D).
    Module SmartContractD := SmartContract(D).

    Definition step (s: StateD.t) (p: SmartContractD.t) : bool :=
        true.

End SmallStep.