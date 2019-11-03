Open Scope list_scope.
Require Import List.

Definition queue (alpha: Set): Set := list alpha * list alpha.

Definition empty (alpha: Set): queue alpha := (nil, nil).

Definition isEmpty {alpha: Set} (q: queue alpha) :=
  match q with
  | (nil, _) => true
  | _ => false
  end.

Definition checkf {alpha: Set} (q: queue alpha) :=
  match q with
  | (nil, r) => (rev r, nil)
  | q' => q'
  end.

Definition fst {alpha: Set} (q: queue alpha) :=
  match q with
  | (f, _) => f
  end.

Definition snd {alpha: Set} (q: queue alpha) :=
  match q with
  | (_, s) => s
  end.

Definition snoc {alpha: Set} (q: queue alpha)(x: alpha) :=
  checkf (fst q, x :: snd q).

Definition head {alpha: Set} (q: queue alpha) :=
  match q with
  | (nil, _) =>  None
  | (x :: f, r) => Some(x)
  end.

Definition tail {alpha: Set} (q: queue alpha) :=
  match q with
  | (nil, _) =>  None
  | (x :: f, r) => Some(checkf (f, r))
  end.

Definition Invaliant {A: Set} (q: queue A) :=
  let '(f, r) := q in
  f = nil -> r = nil.

Lemma snoc_invaliant : forall (A:Set) (q: queue A) (x : A),
    Invaliant q -> Invaliant (snoc q x).
Proof.
  intros A q x H. destruct q as [f r]. unfold snoc, checkf. simpl.
  destruct f.
  - now unfold Invaliant.
  - now unfold Invaliant.
Qed.

Lemma tail_invaliant : forall (A:Set) (q q': queue A),
    Invaliant q -> Some q' = tail q -> Invaliant q'.
Proof.
  intros A q q' H. destruct q as [f r].
  destruct f.
  - now unfold tail.
  - unfold tail, checkf. intros Heq. injection Heq. intros Heq'. clear Heq. subst q'.
    destruct f.
    + now unfold Invaliant.
    + now unfold Invaliant.
Qed.