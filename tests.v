Module Type PARAM.
    Parameter t : Type.
End PARAM.

Module Mod1(P: PARAM).
  Definition t : Type := P.t.
End Mod1.

Module Mod2(P: PARAM).
  (* Definition t : Type := Mod1P.t. *)
    Definition t : Type := P.t.
End Mod2.

Module Mod3(P: PARAM).
  Module Mod1P := Mod1(P).
  Module Mod2P := Mod2(P).
  
  Definition f1 (x : Mod1P.t) : bool := 
    true.

  Definition f2 (x : Mod2P.t) : bool := 
    f1 x.
End Mod3.
