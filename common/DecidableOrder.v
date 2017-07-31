Require common.TotalOrder.
Require common.DecidableEq.

Module Type Seed.
  Parameter T : Set.
  Declare Module DecEqSeed : DecidableEq.Seed with Definition T := T.
  Declare Module OrdSeed : TotalOrder.Seed with Definition T := T.


  Parameter leq_bool : T -> T -> bool.
  Axiom leq_bool_correct : forall x y, leq_bool x y = true <-> OrdSeed.leq x y.
End Seed.

Module Make(S : Seed).
  Include S.
  Module DecEq := DecidableEq.Make(S.DecEqSeed).
  Module Ord := TotalOrder.Make(S.OrdSeed).

  Lemma leq_bool_correct_inv : forall x y, leq_bool x y = false <-> ~ Ord.leq x y.
  Proof.
    intros x y. case_eq (leq_bool x y); intros Heq.
    - split; [discriminate|]. now apply leq_bool_correct in Heq.
    - split; [|reflexivity]. intros _ Hleq. apply leq_bool_correct in Hleq.
      now rewrite Heq in Hleq.
  Qed.

  Definition leq_dec : forall x y, {Ord.leq x y} + {~ Ord.leq x y}.
    intros x y. case_eq (leq_bool x y).
    - intros eq. apply leq_bool_correct in eq. now left.
    - intros eq. right. intro. apply leq_bool_correct in H.
      now rewrite H in eq.
  Qed.

  Definition lt_dec : forall x y, {Ord.lt x y} + {~Ord.lt x y}.
    intros x y. destruct (DecEq.eq_dec x y).
    - right. subst y. now unfold Ord.lt.
    - unfold Ord.lt. now destruct (leq_dec x y); [left| right].
  Qed.

  Module Op.
    Include Ord.Op.
    Infix "=?" := DecEq.eq_dec (at level 70).
    Infix "<=?" := leq_dec (at level 70).
    Infix "<?" := lt_dec (at level 70).
    Infix ">?" := (fun x y => lt_dec y x) (at level 70).
  End Op.

  Definition min x y := if leq_bool x y then x else y.
  Definition max x y := if leq_bool x y then y else x.

  Axiom min_l : forall n m, Ord.leq n m -> min n m = n.
  Axiom min_r : forall n m, Ord.leq m n -> min n m = m.
  Axiom min_assoc: forall m n p, min m (min n p) = min (min m n) p.
  Axiom min_comm: forall n m, min n m = min m n.

End Make.
