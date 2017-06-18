Module Type Ordered.
  Parameter T : Set.
  Parameter eq_bool  : T -> T -> bool.
  Parameter lt_bool  : T -> T -> bool.
  Parameter leq_bool : T -> T -> bool.

  Definition leq x y := (leq_bool x y = true).
  Definition lt x y  := leq x y /\ ~leq y x.

  Axiom eq_bool_correct : forall x y, eq_bool x y = true <-> x = y.

  Axiom lt_bool_correct : forall x y, lt_bool x y = true <-> lt x y.
  Axiom lt_bool_correct_inv : forall x y, lt_bool x y = false <-> ~lt x y.

  Axiom leq_total : forall x y, leq x y \/ leq y x.
  
  Axiom le_lteq : forall x y, leq x y <-> lt x y \/ x=y.
  Axiom Antisymmetric : forall x y, leq x y -> leq y x -> x = y.

  Axiom lt_irrefl : forall x, ~ (lt x x).

  Axiom lt_asymm: forall n m, lt n m -> ~ lt m n.

End Ordered.
