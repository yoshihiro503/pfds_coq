Module Type Ordered.
  Parameter T : Set.
  Parameter eq_bool  : T -> T -> bool.
  Parameter lt_bool  : T -> T -> bool.
  Parameter leq_bool : T -> T -> bool.

  Definition leq x y := (leq_bool x y = true).
  Definition lt x y  := leq x y /\ x <> y.

  Axiom eq_bool_correct : forall x y, eq_bool x y = true <-> x = y.

  Axiom lt_bool_correct : forall x y, lt_bool x y = true <-> lt x y.
  Axiom lt_bool_correct_inv : forall x y, lt_bool x y = false <-> ~lt x y.

  Axiom leq_bool_correct : forall x y, leq_bool x y = true <-> leq x y.
  Axiom leq_bool_correct_inv : forall x y, leq_bool x y = false <-> ~leq x y.

  Axiom leq_total : forall x y, leq x y \/ leq y x.
  
  Axiom le_lteq : forall x y, leq x y <-> lt x y \/ x=y.
  Axiom Antisymmetric : forall x y, leq x y -> leq y x -> x = y.

  Axiom lt_irrefl : forall x, ~ (lt x x).

  Axiom lt_asymm: forall n m, lt n m -> ~ lt m n.

  Axiom le_trans : forall n m p, leq n m -> leq m p -> leq n p.
  Axiom not_le : forall n m, ~ leq n m -> lt m n.
  Axiom lt_not_le : forall n m, lt n m -> ~ leq m n.
  Axiom lt_le_incl : forall n m, lt n m -> leq n m.

  Definition leq_dec : forall x y, {leq x y} + {lt y x}.
    intros x y. case_eq (leq_bool x y).
    - intros eq. now left.
    - intros eq. admit.
    Admitted.
  
  Definition min x y := if eq_bool x y then x else y.
  Definition max x y := if eq_bool x y then y else x.

  Axiom min_l : forall n m, leq n m -> min n m = n.
  Axiom min_r : forall n m, leq m n -> min n m = m.
End Ordered.
