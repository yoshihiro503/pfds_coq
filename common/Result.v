Require Import String.

Definition error := string.

Inductive Result (A: Type) : Type :=
| Ok : A -> Result A
| Error : error -> Result A.

Arguments Ok [A].
Arguments Error [A].