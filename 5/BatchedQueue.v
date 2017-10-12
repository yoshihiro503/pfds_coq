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

