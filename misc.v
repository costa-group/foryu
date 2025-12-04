Require Import Coq.Bool.Bool.

Module Misc.

(* Tactic: "Obtain eqb_eq from reflect" *)
Ltac eqb_eq_from_reflect eqb_spec :=
   (symmetry; apply reflect_iff; apply eqb_spec) || (apply reflect_iff; apply eqb_spec).

Ltac eqb_neq_from_reflect eqb_spec_xy :=
   try (rewrite (reflect_iff _ _ eqb_spec_xy) || rewrite <- not_true_iff_false; eqb_neq_from_reflect eqb_spec_xy);
   reflexivity.

Ltac sumbool_from_reflect eqb_spec_xy :=
  destruct eqb_spec_xy; 
  [ left; assumption  | right; assumption ].

End Misc.
