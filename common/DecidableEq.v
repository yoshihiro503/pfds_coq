Module Type Seed.
  (* === Eq =============== *)
  Parameter T : Set.
  Parameter eq_bool  : T -> T -> bool.

  Axiom eq_bool_correct : forall x y, eq_bool x y = true <-> x = y.

  (* === Eq =============== *)

End Seed.

Module Make(S : Seed).
  Export S.

  Definition eq_dec : forall (x y: T), {x = y} + {x <> y}.
    intros x y. case_eq (eq_bool x y).
    - intros eq. apply eq_bool_correct in eq. now left.
    - intros neq. right. intro. apply eq_bool_correct in H. now rewrite neq in H.
  Defined.
  
End Make.