Require Import Setoid.
Require Import PFDS.common.DecidableOrder.

Module UnbalancedSet (ElementSeed : DecidableOrder.Seed).

  (**
   * 2.2 二分探索木
   *)

  Module Element := DecidableOrder.Make(ElementSeed).
  Definition Elem := Element.T.
  Import Element.Op.

  Inductive Tree : Type :=
  | E : Tree
  | T : Tree -> Elem -> Tree -> Tree.

  Inductive TreeForall (P : Elem -> Prop) : Tree -> Prop :=
  | TreeForallE : TreeForall P E
  | TreeForallT : forall x t1 t2, P x -> TreeForall P t1 -> TreeForall P t2 -> TreeForall P (T t1 x t2).

  Lemma TreeForall_impl : forall (P Q: Elem -> Prop),
      (forall x, P x -> Q x) ->
      forall t, TreeForall P t -> TreeForall Q t.
  Proof.
  Admitted.

  (**
     二分木の要素が対象順(symmetric order)で格納されているということを示す[Prop]。
     「対象順とは任意の与えられたノードの要素が、その左側の部分木の中のどの要素よりも大きく、
     右側の部分木のどの要素よりも小さい、という意味である」
   *)

  Inductive Ordered : Tree -> Prop :=
  | OrderedE : Ordered E
  | OrderedT : forall x t1 t2, Ordered t1 -> Ordered t2 -> TreeForall (fun x1 => x1 < x) t1 -> TreeForall(fun x2 => x < x2) t2 -> Ordered (T t1 x t2).

  (**
     二分木に要素が含まれていることを示す[Prop]。
   *)

  Inductive Member : Elem -> Tree -> Prop :=
  | MemberRoot : forall x t1 t2, Member x (T t1 x t2)
  | MemberBranchLeft : forall x y t1 t2, Member x t1 -> Member x (T t1 y t2)
  | MemberBranchRight : forall x y t1 t2, Member x t2 -> Member x (T t1 y t2).

  Lemma Member_Forall : forall P x t,
      Member x t -> TreeForall P t -> P x.
  Proof.
    intros P x t HMem. induction HMem; intros HForall.
    - now inversion HForall.
    - inversion HForall. now apply IHHMem.
    - inversion HForall. now apply IHHMem.
  Qed.

  (**
     [member]の実装
   *)
  Fixpoint member x tree :=
    match tree with
    | E => false
    | T a y b =>
      if x <? y then member x a
      else if x >? y then member x b
      else true
    end.

  Theorem member_sound : forall x tree,
      Ordered tree -> member x tree = true -> Member x tree.
  Proof.
    intros x tree HOrdered. induction HOrdered.
    - discriminate.
    - simpl. destruct (x <? x0).
      + intros HLeft. apply IHHOrdered1 in HLeft. now apply MemberBranchLeft.
      + destruct (x0 <? x).
        * intros HRight. apply IHHOrdered2 in HRight. now apply MemberBranchRight.
        * intros _. cutrewrite (x = x0); [now constructor|].
          admit.
  Admitted.

  (**
     [insert]の実装
   *)
  Fixpoint insert x tree :=
    match tree with
    | E => T E x E
    | T a y b as s =>
      if x <? y then T (insert x a) y b
      else if x >? y then T a y (insert x b)
      else s
    end.

  (**
   ** 演習問題 2.2 (p. 22)

      member関数を改良して、[lt]の回数が木の深さ[d]に対して[d+1]回になるようにせよ。
   *)

  (**
   *** 関数の実装

       [member2]という名前で実装する。
   *)
  Fixpoint member2_aux x tree candidate :=
    match (tree, candidate) with
    | (E, None) => false
    | (E, Some c) =>
      if x =? c then true else false
    | (T a y b, _) =>
      if x <? y then member2_aux x a candidate
      else member2_aux x b (Some y)
    end.
  Definition member2 x tree := member2_aux x tree None.

  (**
   *** 証明

       [member2]が元の[member]と同様の性質を満たしているかどうかを証明する。
       [member2_aux]で第3引数にくる[cand]が[x]を超えないことを保ったままだんだん大きくなることを考慮して補題をたてる。
   *)
  Lemma member2_aux_sound : forall x t cand,
      member2_aux x t cand = true -> Member x t \/ cand = Some x.
  Proof.
    intros x t. induction t as[| a IHa y b IHb]; intros cand.
    - simpl. destruct cand; [|discriminate].
      destruct (x =? t); [| discriminate]. subst. now right.
    - simpl. destruct (x <? y).
      + (* x<y のとき *)
        intros HLeft. apply IHa in HLeft. destruct HLeft; [left| now right]. now constructor.
      + (* x>=y のとき *)
        intros HRight. apply IHb in HRight.
        destruct HRight; left; [now apply MemberBranchRight| ].
        injection H. intros Hxy. subst. now constructor.
  Qed.

  Lemma member_aux_complete_1 : forall x t,
      Ordered t -> TreeForall (fun e => x <= e) t ->
      member2_aux x t (Some x) = true.
  Proof.
  Admitted.

  Lemma member_aux_complete_2 : forall x t cand,
      Ordered t ->
      Member x t -> member2_aux x t cand = true.
  Proof.
    (* Member の導出木に関する帰納法 *)
    intros x t cand HOrdered Hmem. revert cand. induction Hmem as [| x y a b | x y a b]; intros cand.
    - (* x = y のとき *)
      simpl. destruct (x <? x) as [Hxlt|Hxlt].
      + now destruct (Element.Ord.lt_irrefl x).
      + apply member_aux_complete_1.
        * now inversion HOrdered.
        * inversion HOrdered. subst.
          eapply TreeForall_impl; [|exact H5]. intros e. simpl. unfold Element.Ord.lt. tauto.
    - (* Member x a *)
      inversion HOrdered. subst.
      simpl. destruct (x <? y) as [Hltxy|Hltxy]; [now apply IHHmem | ].
      (* 以降は前提が矛盾するパターン: Hmemよりx < y となるはず、 Hltxyよりy<=xとなる,両者は矛盾 *)
      clear H3 H5. destruct Hltxy.
      now apply (Member_Forall (fun x1 => x1 < y) x a).
    - (* Member x b *)
      inversion HOrdered. subst.
      simpl. destruct (x <? y) as [Hltxy|Hltxy]; [|now apply IHHmem].
      (* 以降は前提が矛盾するパターン: Hmemよりy < x となるはず、 Hltxyよりx<yとなる,両者は矛盾 *)
      clear H2 H4.
      destruct (Element.Ord.lt_asymm x y Hltxy). now apply (Member_Forall (fun x2 => y < x2) _ b).
  Qed.

  Lemma member_aux_complete : forall x t cand,
      Ordered t ->
      (Member x t \/ (cand = Some x /\ TreeForall (fun e => x <= e) t)) -> member2_aux x t cand = true.
  Proof.
    intros x t cand HOrdered H. destruct H.
    - now apply member_aux_complete_2.
    - destruct H. subst. now apply member_aux_complete_1.
  Qed.

  (**
      [member2]関数の結果が[true]ならば性質[Member]を満たす。
   *)
  Theorem member2_sound : forall x t,
      member2 x t = true -> Member x t.
  Proof.
    unfold member2. intros x t Hmem. apply member2_aux_sound in Hmem. now destruct Hmem.
  Qed.

  (**
      性質[Member]を満たすならば[member2]関数の結果が[true]となる。
   *)
  Theorem member2_complete : forall x t,
      Ordered t ->
      Member x t -> member2 x t = true.
  Proof.
    intros x t HOrdered H. unfold member2. now apply member_aux_complete; [| now left].
  Qed.


  (**
   ** 演習問題 2.5
   *)

  (**
   *** 演習問題 2.5 (a)
   *)
  Fixpoint complete x d :=
    match d with
    | O => E
    | S p =>
      let t := complete x p in
      T t x t
    end.

  Inductive CompleteWithDepth : nat -> Tree -> Prop :=
  | CompleteLeaf : CompleteWithDepth 0 E
  | CompleteNode : forall x d t1 t2, CompleteWithDepth d t1 -> CompleteWithDepth d t2 -> CompleteWithDepth (S d) (T t1 x t2)
  .
  Definition Complete (tree : Tree) : Prop := exists d, CompleteWithDepth d tree.

  Theorem complete_sound : forall x d, Complete (complete x d).
  Proof.
    intros x d. exists d. induction d.
    - now constructor.
    - simpl. now constructor.
  Qed.

  (**
   *** 演習問題 2.5 (b)

Scalaでかくと
<<
def create2(m: Int): (Tree,Tree) =
  if (m == 0) (E, T(E, x, E)) else {
    val (t1, t2) = create2((m-1) / 2)
    if ((m-1) % 2 == 0) {
      (T (t1, x, t1), T(t1, x, t2))
    } else {
      (T (t1, x, t2), T(t2, x, t2))
    }
  }

def create(n: Int) = create2(n)._1
>>
   *)

End UnbalancedSet.
