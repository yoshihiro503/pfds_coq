Require Import List Program.
Open Scope list_scope.

Require Import PFDS.common.Ordered.

Declare Module Elem : Ordered.
  
Inductive heap : Set :=
| E : heap
| T : nat -> Elem.T -> heap -> heap -> heap.

Fixpoint right_spine(h : heap) :=
  match h with
  | E => []
  | T r x left_ right_ => x :: right_spine right_
  end.

Definition rank(h : heap) := List.length (right_spine h).

Lemma rank_T : forall r x left_ right_,
    rank(T r x left_ right_) = 1 + rank(right_).
Proof.
  now intros.
Qed.

(** ** Exercise 3.1 *)




