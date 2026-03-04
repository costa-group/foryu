Require Export Coq.Lists.List.
Import ListNotations.

Module ListFunctions.

    Fixpoint option_list {A : Type} (l : list (option A)) : option (list A) :=
    match l with
    | [] => Some []
    | None :: _ => None
    | Some x :: xs =>
        match option_list xs with
        | Some ys => Some (x :: ys)
        | None => None
        end
    end.

End ListFunctions.