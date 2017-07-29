Require Import Program List String.
Require Import PFDS.common.Result.
Open Scope string_scope.
Open Scope list_scope.

Definition pair_size {A B : Set} size1 size2 (pair: A*B) :=
  let '(x, y) := pair in
  size1 x + size2 y.

Definition pipeline {A B: Type} (x: A) (f: A -> B) := f x.
Infix "|>" := pipeline (at level 100).

(* f x y = f y x でかつ f (f x y) z = f x (f y z) であるfに限る *)
Definition reduce_right {A: Type} (f: A -> A -> A) (xs: list A) : Result A :=
  match xs with
  | [] => Error "empty"
  | x :: xs => Ok (List.fold_right f x xs)
  end.

Definition reduce_left {A: Type} (f: A -> A -> A) (xs: list A) : Result A :=
  match xs with
  | [] => Error "empty"
  | x :: xs => Ok (List.fold_left f xs x)
  end.

Definition reduce {A: Type} := @reduce_right A.

 (** proved by chiguri : https://gist.github.com/chiguri/c10948810668490787c5f985f42955bd *)
Lemma fold_right_tail : forall (A B: Type) (f: A -> B -> B) xs x b0,
  List.fold_right f b0 (xs ++ [x]) = List.fold_right f (f x b0) xs.
Proof.
 intros.
 apply List.fold_right_app.
Qed.

(** proved by erutuf : https://gist.github.com/erutuf/123da543af0d6b19ae53bb7e8ccf8b81*)
Lemma fold_right_ext : forall (A : Type)(f g : A -> A -> A) xs x0,
  (forall x y, f x y = g x y) ->
  fold_right f x0 xs = fold_right g x0 xs.
Proof with simpl in *.
  intros.
  induction xs; [auto|]...
  rewrite H.
  rewrite IHxs.
  reflexivity.
Qed.

(** proved by erutuf : https://gist.github.com/erutuf/123da543af0d6b19ae53bb7e8ccf8b81*)
Lemma fold_right_rev : forall (A: Type) (f: A -> A -> A) xs x0,
  (forall x y z, f x (f y z) = f (f x y) z) ->
  (forall x y, f x y = f y x) ->
List.fold_right f x0 xs = List.fold_right f x0 (List.rev xs).
Proof.
  intros.
  rewrite (fold_right_ext _ f (fun x y => f y x)) by auto.
  rewrite <- fold_symmetric; [|auto..].
  rewrite fold_left_rev_right.
  reflexivity.
Qed.

Lemma fold_right_cons_tail : forall (A:Type) (f: A -> A -> A) x xs y ys,
  (forall x y z, f x (f y z) = f (f x y) z) ->
  (forall x y, f x y = f y x) ->
  x :: xs = ys ++ [y] ->
  fold_right f x xs = fold_right f y ys.
Proof.
 intros A f x xs y ys Hassoc Hcomm Heq. destruct xs as [|x1 xs'].
 - destruct ys; [|destruct ys; discriminate Heq]. simpl in Heq. now inversion Heq.
 - destruct ys as [|y1 ys']; [discriminate|].
   inversion Heq. rewrite H1.
   rewrite fold_right_tail. rewrite Hcomm.
   rewrite fold_right_rev at 1; [|assumption|assumption].
   rewrite <- fold_right_tail.
   rewrite fold_right_rev at 1; [|assumption|assumption].
   rewrite rev_unit. now rewrite rev_involutive.
Qed.
