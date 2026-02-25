Require Import Coq.Bool.Bool.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import List Bool.
Require Import ZArith.
Require Import String.
Require Import DecimalString.

Open Scope Z_scope.

Import ListNotations.


Module Misc.

  Definition z_to_string (z : Z) : string :=
  NilEmpty.string_of_int (Z.to_int z).

  Definition n_to_string (n : N) : string :=
  NilEmpty.string_of_uint (N.to_uint n).

  (* Tactic: "Obtain eqb_eq from reflect" *)
  Ltac eqb_eq_from_reflect eqb_spec :=
    (symmetry; apply reflect_iff; apply eqb_spec) || (apply reflect_iff; apply eqb_spec).
  
  Ltac eqb_neq_from_reflect eqb_spec_xy :=
    try (rewrite (reflect_iff _ _ eqb_spec_xy) || rewrite <- not_true_iff_false; eqb_neq_from_reflect eqb_spec_xy);
    reflexivity.
  
  Ltac sumbool_from_reflect eqb_spec_xy :=
    destruct eqb_spec_xy; 
    [ left; assumption  | right; assumption ].
  
  Ltac eqb_eq_to_eq_refl eqb_eq :=
    rewrite eqb_eq; apply eq_refl.
  
  Lemma not_exists_iff_forall_not : forall A (P : A -> Prop),
      (~ exists x, P x) <-> (forall x, ~ P x).
  Proof.
    intros. split.
    - (* Forward: ~ exists -> forall ~ *)
      apply not_ex_all_not.
    - (* Backward: forall ~ -> ~ exists *)
      intros H_all H_ex.
      destruct H_ex as [x H_proof].
      apply (H_all x). (* This gives ~ P x *)
      exact H_proof.
  Qed.

  Section ListInDecidable.
    Variable A : Type.
    Hypothesis eq_dec : forall x y: A, sumbool (x=y) (x<>y).
    
    Lemma prove_in_decidable : forall (x : A) (l' : list A), 
        Decidable.decidable (In x l').
    Proof.
      intros x l'.
      unfold Decidable.decidable.
      destruct (In_dec eq_dec x l') as [H_in | H_not_in].
      - left. exact H_in.
      - right. exact H_not_in.
    Qed.
    End ListInDecidable.
  
  Section NoDupBool.
    Variable A : Type.
    Variable eqb : A -> A -> bool.
    Hypothesis eqb_eq : forall x y, eqb x y = true <-> x = y.
    Hypothesis eq_dec : forall x y: A, sumbool (x=y) (x<>y).

    Fixpoint nodupb (l : list A) : bool :=
      match l with
      | [] => true
      | x :: xs => if existsb (eqb x) xs then false else nodupb xs
      end.
    
    
    Lemma nodupb_spec : forall l, Is_true (nodupb l) -> NoDup l.
    Proof.
      induction l as [|x l' IHl'].
      - simpl. intro. apply NoDup_nil.
      - simpl.
        destruct (existsb (eqb x) l') eqn:E_existsb.
        + intros H_contra.
          unfold Is_true in H_contra.
          contradiction.
        + rewrite <- not_true_iff_false in E_existsb.        
          rewrite (existsb_exists (eqb x) l') in E_existsb.
          rewrite not_exists_iff_forall_not in E_existsb.
          pose proof (E_existsb x) as E_existsb.
          apply Decidable.not_and in E_existsb.
          destruct E_existsb as [H_not_In_x_l' | H_not_eqb_x_x ].
          * intros H_nodupb_l'.
            pose proof (IHl' H_nodupb_l') as H_NoDup_l'.
            apply NoDup_cons; assumption.
          * rewrite eqb_eq in H_not_eqb_x_x.
            contradiction.
          * apply prove_in_decidable.
            apply eq_dec.
    Qed.
  End NoDupBool.

  (* equal lists have equal length *)
  Lemma len_eq:
    forall {A: Type} (x y : list A), x = y -> List.length x = List.length y.
  Proof.
    intros.
    rewrite H.
    reflexivity.
  Qed.


End Misc.
