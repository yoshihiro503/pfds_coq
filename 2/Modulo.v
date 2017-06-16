(* nat上の商と余りを計算する *)

Require Import Arith.
Require Import Euclid.

Definition quotient_modulo :
  forall n,
    n > 0 ->
    forall m:nat, {qr : nat * nat |  let '(q, r) := qr in m = q * n + r /\ n > r}.
Proof.
  induction m as (m,H0) using gt_wf_rec.
  destruct (le_gt_dec n m) as [Hlebn|Hgtbn].
  - destruct (H0 (m - n)) as (qr & Hqr); auto with arith.
    destruct qr as (q, r). exists (S q, r).
    destruct Hqr as (Heq & Hgt). split; [| now trivial].
    simpl. rewrite <- plus_assoc. rewrite <- Heq. now auto with arith.
  - exists (0, m). simpl. now auto with arith.
Defined.

Definition quot_mod x y :=
  match y with
  | O => (O, x)
  | S p =>
    let '(exist (q,r) _) := quotient_modulo (S p) (lt_O_Sn p) x in
    (q, r)
  end.

Theorem quot_mod_sound : forall x y q r,
  y > 0 -> quot_mod x y = (q, r) -> x = q * y + r /\ y > r.
Proof.
  intros x y q r Hgt0. destruct y; [now destruct (gt_irrefl 0)|].
  simpl.
  destruct (quotient_modulo (S y) _ x) as [(q',r') Hr'].
  intros Heq_qr. injection Heq_qr. intros Heq_r Heq_q. subst.
  assumption.
Qed.
                        
                        