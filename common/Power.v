Fixpoint pow m n :=
  match n with
  | O => 1
  | S n' => m * pow m n'
  end.

Lemma pow_le : forall n x y,
    n >= 1 ->
    x <= y <-> pow n x <= pow n y.
Proof.
Admitted.

Lemma pow_plus : forall n x y,
    pow n (x + y) = pow n x * pow n y.
Proof.
Admitted.

Infix "^^" := pow (at level 30, right associativity) : nat_scope.