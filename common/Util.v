Require Import Program List String.
Require Import PFDS.common.Result.
Open Scope string_scope.

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