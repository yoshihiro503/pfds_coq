Require Import Setoid.

Module Type Ordered.

  (* === Eq =============== *)
  Parameter T : Set.
  Parameter eq_bool  : T -> T -> bool.

  Axiom eq_bool_correct : forall x y, eq_bool x y = true <-> x = y.

  Definition eq_dec : forall (x y: T), {x = y} + {x <> y}.
    intros x y. case_eq (eq_bool x y).
    - intros eq. rewrite eq_bool_correct in eq. now left.
    - intros neq. right. intro. rewrite <- eq_bool_correct in H. now rewrite neq in H.
  Defined.
  (* === Eq =============== *)

  Parameter leq : T -> T -> Prop.
  Axiom le_refl : forall x, leq x x.
  Axiom le_trans : forall n m p, leq n m -> leq m p -> leq n p.
  Axiom Antisymmetric : forall x y, leq x y -> leq y x -> x = y.
  Axiom leq_total : forall x y, leq x y \/ leq y x.

  Parameter leq_bool : T -> T -> bool.
  Axiom leq_bool_correct : forall x y, leq_bool x y = true <-> leq x y.

  Definition lt x y  := leq x y /\ x <> y.

  Lemma leq_bool_correct_inv : forall x y, leq_bool x y = false <-> ~leq x y.
  Proof.
    intros x y. case_eq (leq_bool x y); intros Heq.
    - split; [discriminate|]. now apply leq_bool_correct in Heq.
    - split; [|reflexivity]. intros _ Hleq. apply leq_bool_correct in Hleq.
      now rewrite Heq in Hleq.
  Qed.

  Lemma lt_not_le : forall n m, lt n m -> ~ leq m n.
  Proof.
   intros n m Hlt Hleq. unfold lt in Hlt. destruct Hlt. destruct H0. now apply Antisymmetric.
  Qed.

  Lemma not_le_lt : forall n m, ~leq n m -> lt m n.
  Proof.
    intros n m Hnle. destruct (leq_total n m); [now elim Hnle|].
    split; [assumption|]. intro eq. rewrite eq in Hnle. destruct Hnle. apply le_refl.
  Qed.

  Lemma lt_irrefl : forall x, ~ (lt x x).
  Proof.
    intros x. now unfold lt.
  Qed.

  Lemma lt_asymm: forall n m, lt n m -> ~ lt m n.
  Proof.
    intros n m Hlt. unfold lt. now apply lt_not_le in Hlt.
  Qed.

  Lemma lt_le_incl : forall n m, lt n m -> leq n m.
  Proof.
   intros n m. now unfold lt.
  Qed.

  Definition leq_dec : forall x y, {leq x y} + {~leq x y}.
    intros x y. case_eq (leq_bool x y).
    - intros eq. rewrite leq_bool_correct in eq. now left.
    - intros eq. right. intro. rewrite <- leq_bool_correct in H.
      now rewrite H in eq.
  Qed.

  Definition lt_dec : forall x y, {lt x y} + {~lt x y}.
    intros x y. destruct (eq_dec x y).
    - right. subst y. now unfold lt.
    - unfold lt. now destruct (leq_dec x y); [left| right].
  Qed.

  Module Op.
    Infix "=?" := eq_dec (at level 70).
    Infix "<=?" := leq_dec (at level 70).
    Infix "<?" := lt_dec (at level 70).
    Infix ">?" := (fun x y => lt_dec y x) (at level 70).
  End Op.

  Definition min x y := if leq_bool x y then x else y.
  Definition max x y := if leq_bool x y then y else x.

  Axiom min_l : forall n m, leq n m -> min n m = n.
  Axiom min_r : forall n m, leq m n -> min n m = m.
  Axiom min_assoc: forall m n p, min m (min n p) = min (min m n) p.
  Axiom min_comm: forall n m, min n m = min m n.

End Ordered.
