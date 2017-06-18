Require Import List Program Arith.
Open Scope list_scope.

Require Import PFDS.common.Ordered.
Require Import PFDS.common.Power.

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

Fixpoint size(h : heap) :=
  match h with
  | E => 0
  | T _ _ a b => 1 + size(a) + size(b)
  end.

Inductive Leftist : heap -> Prop :=
| LeftistE : Leftist E
| LeftistT : forall a b r x,
    rank b <= rank a -> Leftist a -> Leftist b -> Leftist (T r x a b).

(** ** Exercise 3.1 *)

Lemma ex3_1_aux : forall t, Leftist t -> 2 ^^ (rank t) <= size t + 1.
Proof.
  induction t as[| r x a IHa b IHb].
  - reflexivity.
  - rewrite rank_T. simpl size. intro HLeftist.
    cutrewrite (S (size a + size b) + 1 = (size a + 1) + (size b + 1)); [| ring].
    inversion HLeftist as [|a0 b0 r0 x0 Hrank HLa HLb]. subst. apply IHa in HLa. apply IHb in HLb.
    apply (le_trans _ (pow 2 (rank a) + (size b + 1))); [|now apply plus_le_compat_r].
    apply (le_trans _ (pow 2 (rank a) + pow 2 (rank b))); [|now apply plus_le_compat_l].
    rewrite pow_plus. simpl (pow 2 1).
    cutrewrite (2 * pow 2 (rank b) = pow 2 (rank b) + pow 2 (rank b)); [|ring].
    apply (plus_le_compat_r). now apply pow_le; [now auto with arith|].
Qed.


