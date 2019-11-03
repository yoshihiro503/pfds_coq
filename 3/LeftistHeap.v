Require Import List Program Arith String.
Open Scope string_scope.
Open Scope list_scope.

Require Import PFDS.common.DecidableOrder.
Require Import PFDS.common.Power.
Require Import PFDS.common.Result.
Require Import PFDS.common.Util.

Declare Module Seed : DecidableOrder.Seed.
Module Elem := DecidableOrder.Make(Seed).
Import Elem.Op.
  
Inductive heap : Set :=
| E : heap
| T : nat -> Elem.T -> heap -> heap -> heap.

Inductive HeapForall (P : Elem.T -> Prop) : heap -> Prop :=
| HFE : HeapForall P E
| HFT : forall r x a b, HeapForall P a -> HeapForall P b -> P x -> HeapForall P (T r x a b).

Lemma HeapForall_impl : forall (P Q: Elem.T -> Prop),
    (forall x, P x -> Q x) ->
    forall h, HeapForall P h -> HeapForall Q h.
Proof.
  intros P Q Hpq h HForallP. induction HForallP.
  - now constructor.
  - now constructor; [| | apply Hpq].
Qed.

Fixpoint right_spine(h : heap) :=
  match h with
  | E => []
  | T r x left_ right_ => x :: right_spine right_
  end.

Definition calc_rank(h : heap) := List.length (right_spine h).

Lemma rank_T : forall r x left_ right_,
    calc_rank(T r x left_ right_) = 1 + calc_rank(right_).
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
    (calc_rank b <= calc_rank a)%nat -> Leftist a -> Leftist b -> Leftist (T r x a b).

(** ** Exercise 3.1 *)

Lemma ex3_1_aux : forall t, Leftist t -> (2 ^^ (calc_rank t) <= size t + 1)%nat.
Proof.
  induction t as[| r x a IHa b IHb].
  - reflexivity.
  - rewrite rank_T. simpl size. intro HLeftist.
    cutrewrite (S (size a + size b) + 1 = (size a + 1) + (size b + 1)); [| ring].
    inversion HLeftist as [|a0 b0 r0 x0 Hrank HLa HLb]. subst. apply IHa in HLa. apply IHb in HLb.
    apply (le_trans _ (pow 2 (calc_rank a) + (size b + 1))); [|now apply plus_le_compat_r].
    apply (le_trans _ (pow 2 (calc_rank a) + pow 2 (calc_rank b))); [|now apply plus_le_compat_l].
    rewrite pow_plus. simpl (pow 2 1).
    cutrewrite (2 * pow 2 (calc_rank b) = pow 2 (calc_rank b) + pow 2 (calc_rank b)); [|ring].
    apply (plus_le_compat_r). now apply pow_le; [now auto with arith|].
Qed.

(**
   ** merge関数
   > どの右スパインの長さもたかだか対数のオーダーであるから、[merge]は O(log n) 時間で実行される。 (p.28)
 *)

(**
   *** merge関数の実装
 *)

Definition rank h :=
  match h with
  | E => 0
  | T r _ _ _ => r
  end.

Definition makeT x a b :=
  if le_lt_dec (rank b) (rank a) then T (1 + rank b) x a b
  else T (1 + rank a) x b a.

Require Import Recdef.

Function merge h1_h2 {measure (pair_size size size) h1_h2} :=
  match (h1_h2) with
  | (E, h2) => h2
  | (h1, E) => h1
  | (T _ x a1 b1 as h1, T _ y a2 b2 as h2) =>
    if Elem.leq_bool x y then
      makeT x a1 (merge (b1, h2))
    else
      makeT y a2 (merge (h1, b2))
  end.
Proof. (* 停止性の証明 *)
  - simpl. now auto with arith.
  - simpl. now auto with arith.
Defined.

(**
   *** merge関数の証明
*)

(**
   **** merge関数でrank関数の健全性が保たれる
*)

Inductive RankSound : heap -> Prop :=
| RSE : RankSound E
| RST : forall r x a b, RankSound a -> RankSound b -> rank (T r x a b) = calc_rank (T r x a b) -> RankSound(T r x a b).

Lemma RankSound_eq : forall h,
    RankSound h -> rank h = calc_rank h.
Proof.
  intros h Hrank. now induction Hrank.
Qed.

Lemma makeT_rank : forall x a b,
  RankSound a -> RankSound b ->
    RankSound (makeT x a b).
Proof.
  intros x a b Hranka Hrankb. unfold makeT.
  destruct (le_lt_dec (rank b) (rank a)).
  - constructor; [assumption| assumption|]. rewrite rank_T. now rewrite (RankSound_eq _ Hrankb).
  - constructor; [assumption| assumption|]. rewrite rank_T. now rewrite (RankSound_eq _ Hranka).
Qed.

Lemma merge_rank : forall h1 h2,
  RankSound h1 -> RankSound h2 -> RankSound (merge (h1,h2)).
Proof.
  cut (forall h1h2, RankSound (fst h1h2) -> RankSound (snd h1h2) -> RankSound (merge h1h2)); [intros; now apply H|].
  intros h1h2. apply merge_ind.
  - now intros.
  - now intros.
  - simpl. intros h1_h2 _r1 x a1 b1 _r2 y a2 b2 Heq Hleq IH Hrank1 Hrank2. subst.
    inversion Hrank1. inversion Hrank2. subst.
    apply makeT_rank; [assumption|]. now apply IH.
  - simpl. intros h1_h2 _r1 x a1 b1 _r2 y a2 b2 Heq Hleq IH Hrank1 Hrank2. subst.
    inversion Hrank1. inversion Hrank2. subst.
    apply makeT_rank; [assumption|]. now apply IH.
Qed.

(**
   **** merge関数でLeftist性が保存される
*)

Lemma makeT_Leftist : forall x a b,
    RankSound a -> RankSound b ->
    Leftist a -> Leftist b ->
    Leftist (makeT x a b).
Proof.
  intros x a b Hra Hrb Hla Hlb. unfold makeT.
  destruct (le_lt_dec _ _).
  - constructor; [|assumption|assumption].
    now rewrite <- (RankSound_eq _ Hrb), <- (RankSound_eq _ Hra).
  - constructor; [|assumption|assumption].
    apply lt_le_weak. now rewrite <- (RankSound_eq _ Hrb), <- (RankSound_eq _ Hra).
Qed.

Lemma merge_Leftist : forall h1 h2,
      RankSound h1 -> RankSound h2 ->
      Leftist h1 -> Leftist h2 ->
      Leftist (merge (h1, h2)).
Proof.
  cut (forall h1h2, RankSound (fst h1h2) -> RankSound (snd h1h2) -> Leftist (fst h1h2) -> Leftist (snd h1h2) -> Leftist (merge h1h2)); [intros; now apply H|].
  intros h1h2. apply merge_ind.
  - now intros.
  - now intros.
  - simpl. intros h1_h2 _r1 x a1 b1 _r2 y a2 b2 Heq _ IH Hr1 Hr2 Hl1 Hl2.
    inversion Hr1. inversion Hl1. subst.
    inversion Hr2. inversion Hl2. subst.
    apply makeT_Leftist; [assumption| | assumption|].
    + now apply merge_rank.
    + now apply IH.
  - simpl. intros h1_h2 _r1 x a1 b1 _r2 y a2 b2 Heq _ IH Hr1 Hr2 Hl1 Hl2.
    inversion Hr1. inversion Hl1. subst.
    inversion Hr2. inversion Hl2. subst.
    apply makeT_Leftist; [assumption | | assumption|].
    + now apply merge_rank.
    + now apply IH.
Qed.

(**
   **** merge関数とHeapForallのいい関係
*)

Lemma makeT_Forall : forall P x a b,
    (HeapForall P a /\ HeapForall P b /\ P x) <-> HeapForall P (makeT x a b).
Proof.
  intros P x a b. unfold makeT. destruct (le_lt_dec _ _); split; intros.
  + now constructor.
  + now inversion H.
  + now constructor.
  + now inversion H.
Qed.

Lemma merge_Forall : forall P h1 h2,
    (HeapForall P h1 /\ HeapForall P h2) <-> HeapForall P (merge (h1,h2)).
Proof.
  intros P. cut (forall p, HeapForall P (fst p) /\ HeapForall P (snd p) <-> HeapForall P (merge p)); [intros; now destruct (H (h1,h2))|].
  intros h1h2. apply merge_ind.
  - intros. simpl. split; [tauto|]. now split; [constructor | ].
  - intros. simpl. split; [tauto|]. now split; [ | constructor].
  - simpl. intros h1_h2 _r1 x a1 b1 _r2 y a2 b2 Heq _ IH.
    rewrite <- makeT_Forall. rewrite <- IH. split.
    + intros H. destruct H as [H1 H2]. inversion H1. now inversion H2.
    + intros H. split; [|tauto]. now constructor.
  - simpl. intros h1_h2 _r1 x a1 b1 _r2 y a2 b2 Heq _ IH.
    rewrite <- makeT_Forall. rewrite <- IH. split.
    + intros H. destruct H as [H1 H2]. inversion H1. now inversion H2.
    + intros H. split; [tauto|]. now constructor.
Qed.


(**
   **** merge関数でヒープとしての性質: 「常にrootノードの値が最小値」を保存することを証明
*)

Inductive Heap : heap -> Prop :=
| HeapE : Heap E
| HeapT : forall r x a b, Heap a -> Heap b -> HeapForall (fun elem => x <= elem) (T r x a b) -> Heap (T r x a b).

Lemma makeT_Heap : forall x a b,
    Heap a -> Heap b ->
    HeapForall (fun elem => x <= elem) a ->
    HeapForall (fun elem => x <= elem) b ->
    Heap (makeT x a b).
Proof.
Admitted.

Lemma merge_Heap : forall h1 h2,
    Heap h1 -> Heap h2 ->
    Heap (merge (h1,h2)).
Proof.
  cut (forall p, Heap (fst p) -> Heap (snd p) -> Heap (merge p)); [intros; now apply H|].
  intro h1h2. apply merge_ind.
  - now intros.
  - now intros.
  - simpl. intros h1_h2 _r1 x a1 b1 _r2 y a2 b2 Heq Hleq IH Hh1 Hh2.
    inversion Hh1. inversion Hh2. subst.
    inversion H5. inversion H12. subst.
    apply makeT_Heap; [assumption| now apply IH|assumption|].
    apply merge_Forall. split; [assumption |].
    eapply HeapForall_impl; [|now apply H12]. simpl. intros elem Helem.
    apply (Elem.Ord.le_trans _ y); [|assumption]. now apply Elem.leq_bool_correct.
  - simpl. intros h1_h2 _r1 x a1 b1 _r2 y a2 b2 Heq Hleq IH Hh1 Hh2.
    inversion Hh1. inversion Hh2. subst.
    inversion H5. inversion H12. subst.
    apply makeT_Heap; [assumption| now apply IH|assumption|].
    apply merge_Forall. split; [| assumption].
    rewrite Elem.leq_bool_correct_inv in Hleq. apply Elem.Ord.not_le_lt in Hleq. apply Elem.Ord.lt_le_incl in Hleq.
    constructor.
    + eapply HeapForall_impl; [ |now apply H3]. simpl. intros elem Helem.
      now apply (Elem.Ord.le_trans _ x).
    + eapply HeapForall_impl; [ |now apply H7]. simpl. intros elem Helem.
      now apply (Elem.Ord.le_trans _ x).
    + assumption.
Qed.

(**
   ** insert
*)

(**
   *** insert関数の実装
*)

Definition insert x h := merge (T 1 x E E, h).

(**
   ** findMin
*)

(**
   *** findMin 関数の実装
*)

Definition findMin h :=
  match h with
  | E => Error "Empty Heap"
  | T _ x _ _ => Ok x
  end.

(**
   ** deleteMin
*)

(**
   *** deleteMin関数の実装
*)

Definition deleteMin h :=
  match h with
  | E => Error "Empty Heap"
  | T _ _ a b => Ok (merge(a, b))
  end.
