Require Import String.

Definition error := string.

Inductive Result (A: Type) : Type :=
| Ok : A -> Result A
| Error : error -> Result A.

Arguments Ok [A].
Arguments Error [A].

Definition ret {A:Type} x : Result A := Ok x.

Definition bind {A B:Type} (m: Result A) (f: A -> Result B) :=
  match m with
  | Ok x => f x
  | Error message => Error message
  end.

Infix ">>=" := bind (at level 100).