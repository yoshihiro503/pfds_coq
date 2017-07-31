Module Type Seed.
  Parameter T : Set.
  Parameter leq : T -> T -> Prop.
  Axiom le_refl : forall x, leq x x.
  Axiom le_trans : forall n m p, leq n m -> leq m p -> leq n p.
  Axiom Antisymmetric : forall x y, leq x y -> leq y x -> x = y.
  Axiom leq_total : forall x y, leq x y \/ leq y x.

End Seed.

Module Make(S : Seed).
  Include S.
  
  Definition lt x y  := leq x y /\ x <> y.

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

  Module Op.
    Infix "<=" := leq.
    Infix "<" := lt.
  End Op.
End Make.
