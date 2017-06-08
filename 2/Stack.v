Require Import Program.
Require Import Result.
Open Scope string_scope.
Open Scope list_scope.

Definition Stack (A: Set) := list A.

Definition empty {A: Set} : Stack A := nil.

Definition isEmpty {A: Set} (s : Stack A) :=
  match s with
  | [] => true
  | _ => false
  end.

Definition cons {A: Set} (x: A) (xs: Stack A) : Stack A := cons x xs.

Definition head {A: Set} (xs: Stack A) : Result A :=
  match xs with
  | [] => Error ""
  | x :: _ => Ok x
  end.

Definition tail {A: Set} (xs: Stack A) : Result (Stack A) :=
  match xs with
  | [] => Error ""
  | _ :: xs => Ok xs
  end.

