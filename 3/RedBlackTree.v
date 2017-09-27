Require Import Program Arith String List.
Require Import Recdef.
Open Scope string_scope.
Open Scope list_scope.

Require Import PFDS.common.Util.
Require Import PFDS.common.DecidableOrder.
Require Import PFDS.common.Result.

Declare Module Seed : DecidableOrder.Seed.
Module Elem := DecidableOrder.Make(Seed).
Import Elem.Op.

(**
 ** 赤黒木(Red Black Tree)

    #<img width="100%" src="http://raw.github.o-in.dwango.co.jp/Yoshihiro-Imai/pfds_coq/master/imgs/redblacktree_sample.jpg" />#
 *)

Inductive color := 赤 | 黒.

Inductive tree : Set :=
| E : tree
| T : color -> tree -> Elem.T -> tree -> tree.

Inductive IsRootBlack : tree -> Prop :=
| BlackE : IsRootBlack E
| BlackT : forall a b x, IsRootBlack (T 黒 a x b).
Hint Constructors IsRootBlack.

(**
 *** tree型の値が赤黒木となっているかという述語

 - ここでいうLengthは経路に含まれる黒ノードの数(赤黒木の全ての経路で黒ノードの数は同じ)
 - treeのElem.Tの順序については何も言っていない
 *)

(*
Inductive RedBlackWithLength : nat -> tree -> Prop :=
| RBEmpty : RedBlackWithLength 0 E
| RBRed : forall x a b n,
    RedBlackWithLength n a -> RedBlackWithLength n b ->
    IsRootBlack a -> IsRootBlack b ->
      RedBlackWithLength n (T 赤 a x b)
| RBBlack : forall x a b n,
    RedBlackWithLength n a -> RedBlackWithLength n b ->
      RedBlackWithLength (1+n) (T 黒 a x b)
.
*)

(* 赤黒木の条件1: すべての経路において黒の数が同一である([n]個) *)
Inductive BalancedWithLength : nat -> tree -> Prop :=
| BE : BalancedWithLength 0 E
| BRed : forall n x a b, BalancedWithLength n a -> BalancedWithLength n b -> BalancedWithLength n (T 赤 a x b)
| BBlack : forall n x a b, BalancedWithLength n a -> BalancedWithLength n b -> BalancedWithLength (1+n) (T 黒 a x b)
.
Hint Constructors BalancedWithLength.

(* 赤黒木の条件2: すべての経路に置いて赤が2連続で現れない *)
Inductive WellColored : tree -> Prop :=
| CE : WellColored E
| CRed : forall a x b,
    WellColored a -> WellColored b -> IsRootBlack a -> IsRootBlack b ->
    WellColored (T 赤 a x b)
| CBlack : forall a x b,
    WellColored a -> WellColored b -> WellColored (T 黒 a x b)
.
Hint Constructors WellColored.

(**
 ** 演習 3.8

    次のような方針でいけそう:
<<
  // 赤黒木のサイズの最小値は黒しか持たない木 (完全木)
  size (t) >= 2^(黒depth(t)) - 1
  // 両辺 +1 して logをとると
  log (size(t) + 1) >= log (2^(黒depth(t)) - 1 + 1)
    (右辺) = 黒depth(t)
  // 両辺 floor をとると
  |_ log(size(t) + 1 _| >= |_ 黒depth(t) _| = 黒depth(t)
  // 上記の depth(t) <= 2 * 黒depth(t) より
    (右辺) >= depth(t) / 2
  // 両辺2倍して 2|_ log(size(t) + 1 _| >= depth(t)
>>
 *)

(**
 ** insert
 *)

(**
 *** [insert]関数の定義
 *)

Definition balance color t1 e t2 :=
  match (color, t1, e, t2) with
  | (黒, T 赤 (T 赤 a x b) y c, z, d)
  | (黒, T 赤 a x (T 赤 b y c), z, d)
  | (黒, a, x, T 赤 (T 赤 b y c) z d)
  | (黒, a, x, T 赤 b y (T 赤 c z d))
      => T 赤 (T 黒 a x b) y (T 黒 c z d)
  | _ => T color t1 e t2
  end.

Fixpoint ins x s :=
  match s with
  | E => T 赤 E x E
  | T color a y b =>
    if x <? y then balance color (ins x a) y b
    else if y <? x then balance color a y (ins x b)
    else s
  end.

Definition insert (x: Elem.T) (s: tree) : tree :=
  match ins x s with
  | T _ a y b => T 黒 a y b
  | E => E (* 本来ここには来得ないパターン *)
  end.

Functional Scheme ins_ind := Induction for ins Sort Prop.

(**
    [balance]関数で場合分けを簡単にするための補題。
 *)
Lemma balance_aux : forall (P : (color*tree*Elem.T*tree) -> tree -> Prop),
  (forall a b c d x y z,
      P (黒, T 赤 (T 赤 a x b) y c, z, d) (T 赤 (T 黒 a x b) y (T 黒 c z d))) ->
  (forall a b c d x y z,
      P (黒, T 赤 a x (T 赤 b y c), z, d) (T 赤 (T 黒 a x b) y (T 黒 c z d))) ->
  (forall a b c d x y z,
      P (黒, a, x, T 赤 (T 赤 b y c) z d) (T 赤 (T 黒 a x b) y (T 黒 c z d))) ->
  (forall a b c d x y z,
      P (黒, a, x, T 赤 b y (T 赤 c z d)) (T 赤 (T 黒 a x b) y (T 黒 c z d))) ->
  (forall col t1 e t2, P (col,t1,e,t2) (T col t1 e t2)) ->
  forall col t1 e t2, P (col,t1,e,t2) (balance col t1 e t2).
Proof.
 intros P H1 H2 H3 H4 Hother col t1 e t2.
 set (Hother col t1 e t2).
 destruct col; [now auto|].
 (destruct t1 as [|c1 t11 x1 t12]; [|destruct c1;
                                     (destruct t11 as [|c11 t11_1 x11 t11_2]; [|destruct c11]);
                                     (destruct t12 as [|c12 t12_1 x12 t12_2]; [|destruct c12])
                                   ]);
   (destruct t2 as [|c2 t21 x2 t22]; [|destruct c2;
                                       (destruct t21 as [|c21 t21_1 x21 t21_2]; [|destruct c21]);
                                       (destruct t22 as [|c22 t22_1 x22 t22_2]; [|destruct c22])
  ]); unfold balance; try (now auto).
Qed.

(**
 *** insertに関する証明
 *)

(**
 **** insertが不変条件2の「すべての経路で黒の数が同一」を保つことを証明
 *)

Lemma balance_Balanced : forall n color elem t1 t2,
  BalancedWithLength n (T color t1 elem t2) -> BalancedWithLength n (balance color t1 elem t2)
.
Proof.
  intros n col e t1 t2.
  apply (balance_aux (fun '(col,t1,e,t2) t =>
                    BalancedWithLength n (T col t1 e t2)->BalancedWithLength n t));
    intros; subst.
  - inversion H. inversion H3. inversion H9.  subst. constructor; now constructor.
  - inversion H. inversion H3. inversion H11. subst. constructor; now constructor.
  - inversion H. inversion H5. inversion H9.  subst. constructor; now constructor.
  - inversion H. inversion H5. inversion H11. subst. constructor; now constructor.
  - assumption.
Qed.

Lemma ins_Balanced : forall n x t,
    BalancedWithLength n t -> BalancedWithLength n (ins x t).
Proof.
  intros n x t. revert n. apply ins_ind.
  - (* t = Eのとき *)
    intros _ _ n HBt. inversion HBt. constructor; now constructor.
  - (* x < y のとき *)
    intros _ col a y b _ Hlt _ IHa n HBt.
    apply balance_Balanced. inversion HBt; subst.
    + (* 赤のとき *)
      constructor; now auto.
    + (* 黒のとき *)
      constructor; now auto.
  - (* y < x のとき *)
    intros _ col a y b _ _ _ Hlt _ IHb n HBt.
    apply balance_Balanced. inversion HBt; subst.
    + (* 赤のとき *)
      constructor; now auto.
    + (* 黒のとき *)
      constructor; now auto.
  - (* ~x < y かつ ~y < x のとき (すなわち x = y) *)
    intros s col a y b eq Hnotlt1 _ Hnotlt2 _ n HBt. subst. assumption.
Qed.

Lemma insert_Balanced : forall n x t,
    BalancedWithLength n t -> exists m, BalancedWithLength m (insert x t).
Proof.
  intros n x t HBal. unfold insert.
  destruct (ins_Balanced n x _ HBal) as [|n e t1 t2|n e t1 t2].
  - now exists 0.
  - exists (1 + n). now constructor.
  - exists (1 + n). now constructor.
Qed.

(**
 **** insertが不変条件1の「赤が2連続で現れない」を保つことを証明
 *)

Lemma balance_color_changed : forall a b y e t1 t2,
  balance 黒 a y b = T 赤 t1 e t2 -> IsRootBlack t1 /\ IsRootBlack t2.
Proof.
  intros a b y e t1 t2.
  apply (balance_aux (fun '(col,t1',e',t2') t => col = 黒 -> balance 黒 a y b = t -> t = T 赤 t1 e t2 -> IsRootBlack t1 /\ IsRootBlack t2)).
  - intros a' b' c' d' x' y' z' Hcol Heq. simpl.
    inversion 1. split; now constructor.
  - intros a' b' c' d' x' y' z' Hcol Heq. simpl.
    inversion 1. split; now constructor.
  - intros a' b' c' d' x' y' z' Hcol Heq. simpl.
    inversion 1. split; now constructor.
  - intros a' b' c' d' x' y' z' Hcol Heq. simpl.
    inversion 1. split; now constructor.
  - intros col t1' e' t2' Hcol Heq. inversion 1. now subst.
  - reflexivity.
  - reflexivity.
Qed.

Lemma ins_color_changed : forall t x e t1 t2,
  WellColored t -> IsRootBlack t ->
  ins x t = T 赤 t1 e t2 -> IsRootBlack t1 /\ IsRootBlack t2.
Proof.
  intros t x e t1 t2 HC HBt. inversion HBt as [|a b y].
  - (* t = E *)
    simpl. inversion 1. split; now constructor.
  - (* t = T 黒 a y bのとき *)
    simpl. destruct (x <? y); [|destruct (y <? x)].
    + (* x < y *)
      now apply balance_color_changed.
    + (* y < x *)
      now apply balance_color_changed.
    + (* x = y *)
      now inversion 1.
Qed.

Lemma balance_Colored_a : forall col_a a1 x a2 y b,
    balance 黒 (T col_a a1 x a2) y b = T 黒 (T col_a a1 x a2) y b ->
    WellColored a1 -> WellColored a2 -> WellColored b -> WellColored (T col_a a1 x a2).
Proof.
  intros col_a a1 x a2 y b Hbal Ca1 Ca2 Cb. destruct col_a.
  - (* a 赤の時 *)
    constructor; auto.
    + destruct a1; [now constructor|]. destruct c; [now inversion Hbal|now constructor].
    + destruct a2; [now constructor|]. destruct c; [|now constructor].
      unfold balance in Hbal. destruct a1; [|destruct c]; now inversion Hbal.
  - (* a 黒の時 *)
    now constructor.
Qed.
  
Lemma balance_Colored_b : forall a y col_b b1 x b2,
    balance 黒 a y (T col_b b1 x b2) = T 黒 a y (T col_b b1 x b2) ->
    WellColored b1 -> WellColored b2 -> WellColored a -> WellColored (T col_b b1 x b2).
Proof.
  intros a y col_b b1 x b2 Hbal Cb1 Cb2 Ca. destruct col_b.
  - (* b 赤の時 *)
    constructor; auto.
    + destruct b1; [now constructor|]. destruct c; [|now constructor].
      unfold balance in Hbal. destruct a as [|[|] [|[|] a11 e1 a12] e [|[|] a21 e2 a22]]; now inversion Hbal.
    + destruct b2; [now constructor|]. destruct c; [|now constructor].
      unfold balance in Hbal.
      destruct a as [|[|] [|[|] a11 e1 a12] e [|[|] a21 e2 a22]], b1 as [|[|] b11 x1 b12]; now inversion Hbal.
  - (* b 黒の時 *)
    now constructor.
Qed.

Lemma ins_Colored : forall x t,
  WellColored t ->
  exists t1 t2 e col, ins x t = T col t1 e t2 /\ WellColored t1 /\ WellColored t2.
Proof.
  intros x t. apply ins_ind.
  - (* t = E *)
    intros _ _ HC. exists E, E, x, 赤. now split; [|split].
  - (* t = T col a y b で x < y *)
    intros _ col a y b _ Hlt _ IHa HC.
    cut (WellColored a); [intros HCa| now inversion HC].
    cut (WellColored b); [intros HCb| now inversion HC].
    destruct (IHa HCa) as [t1 [t2 [e [col_a [Heq [HCt1 HCt2]]]]]].
    apply (balance_aux (fun '(col', a', y', b') t => col'=col /\ a'=(ins x a) /\ y'=y /\ b'=b ->
      balance col (ins x a) y b = t ->
      exists t1 t2 e col0, 
      t = T col0 t1 e t2 /\ WellColored t1 /\ WellColored t2)).
    + (* もみほぐしがおきるときその1 *)
      intros a' b' c' d' x' y' z' [Hcol [Hins [Hz Hd]]] Hbalance. subst z' d' col.
      exists (T 黒 a' x' b'), (T 黒 c' y b), y', 赤.
      split; [reflexivity|]. rewrite Heq in Hins. inversion Hins. subst.
      split; [constructor; now inversion HCt1|now constructor].
    + (* もみほぐしがおきるときその2 *)
      intros a' b' c' d' x' y' z' [Hcol [Hins [Hz Hd]]] Hbalance. subst z' d' col.
      exists (T 黒 a' x' b'), (T 黒 c' y b), y', 赤.
      split; [reflexivity|]. rewrite Heq in Hins. inversion Hins. subst.
      inversion HCt2. split; now constructor.
    + (* もみほぐしがおきるときその3 *)
      intros a' b' c' d' x' y' z' [Hcol [Hins [Hz Hd]]] Hbalance. subst a' x' col.
      rewrite <- Hd in HCb. now inversion HCb.
    + (* もみほぐしがおきるときその4 *)
      intros a' b' c' d' x' y' z' [Hcol [Hins [Hz Hd]]] Hbalance. subst a' x' col.
      rewrite <- Hd in HCb. now inversion HCb.
    + (* もみほぐさないとき *)
      intros col' a' y' b' [Hcol [Hins [Hy' Hb']]]. subst.
      exists (ins x a), b, y, col. split; [reflexivity| ]. split;[ |assumption].
      rewrite Heq. rewrite Heq in H. destruct col.
      * (* col赤の時 *)
        inversion HC. subst. destruct col_a; [| now constructor].
        destruct (ins_color_changed a x e t1 t2 H3 H5 Heq) as [Bt1 Bt2].
        now constructor.
      * (* col黒の時 *)
        now apply (balance_Colored_a col_a t1 e t2 y b).
    + tauto.
    + reflexivity.
  - (* t = T col a y b で x > y *)
    intros _ col a y b _ _ _ _ _ IHb HC.
    cut (WellColored a); [intros HCa| now inversion HC].
    cut (WellColored b); [intros HCb| now inversion HC].
    destruct (IHb HCb) as [t1 [t2 [e [col_b [Heq [HCt1 HCt2]]]]]].
    apply (balance_aux (fun '(col', a', y', b') t => col'=col /\ a'=a /\ y'=y /\ b'=(ins x b) ->
      balance col a y (ins x b) = t ->
      exists t1 t2 e col0, 
      t = T col0 t1 e t2 /\ WellColored t1 /\ WellColored t2)).
    + (* もみほぐしがおきるときその1 *)
      intros a' b' c' d' x' y' z' [Hcol [Hins [Hz Hd]]] Hbalance. subst z' d' col.
      rewrite <- Hins in HCa. now inversion HCa.
    + (* もみほぐしがおきるときその2 *)
      intros a' b' c' d' x' y' z' [Hcol [Hins [Hz Hd]]] Hbalance. subst z' d' col.
      rewrite <- Hins in HCa. now inversion HCa.
    + (* もみほぐしがおきるときその3 *)
      intros a' b' c' d' x' y' z' [Hcol [Ha [Hx Hins]]] Hbalance. subst a' x' col.
      exists (T 黒 a y b'), (T 黒 c' z' d'), y', 赤.
      split; [reflexivity|]. rewrite Heq in Hins. inversion Hins. subst.
      inversion HCt1. split; now constructor.
    + (* もみほぐしがおきるときその4 *)
      intros a' b' c' d' x' y' z' [Hcol [Ha [Hx Hins]]] Hbalance. subst a' x' col.
      exists (T 黒 a y b'), (T 黒 c' z' d'), y', 赤.
      split; [reflexivity|]. rewrite Heq in Hins. inversion Hins. subst.
      inversion HCt2. split; now constructor.
    + (* もみほぐさないとき *)
      intros col' a' y' b' [Hcol [Ha [Hy' Hins]]]. subst.
      exists  a, (ins x b), y, col. split; [reflexivity| ]. split;[assumption|].
      rewrite Heq. rewrite Heq in H. destruct col.
      * (* col赤の時 *)
        inversion HC. subst. destruct col_b; [| now constructor].
        destruct (ins_color_changed b x e t1 t2 H4 H6 Heq) as [Bt1 Bt2].
        now constructor.
      * (* col黒の時 *)
        now apply (balance_Colored_b a y col_b t1 e t2).
    + tauto.
    + reflexivity.
  - (* t = T col a y b で x = y *)
    intros s col a y b Hs _ _ _ _ HC. subst s. exists a, b, y, col.
    cut (WellColored a); [intros HCa| now inversion HC].
    cut (WellColored b); [intros HCb| now inversion HC].
    tauto.
Qed.

Lemma insert_Colored : forall x t,
  WellColored t ->
  WellColored (insert x t).
Proof.
  intros x t HCt. unfold insert.
  destruct (ins_Colored x _ HCt) as [t1 [t2 [e [col [Heq [HCt1 HCt2]]]]]].
  rewrite Heq. now constructor.
Qed.

(**
 **** [insert]で木の順序が崩れていないことを証明
 *)

Inductive TreeForall (P : Elem.T -> Prop) : tree -> Prop :=
| TreeForallE : TreeForall P E
| TreeForallT : forall col t1 x t2, P x -> TreeForall P t1 -> TreeForall P t2 -> TreeForall P (T col t1 x t2).
Hint Constructors TreeForall.

Lemma TreeForall_impl : forall (P Q: Elem.T -> Prop),
    (forall x, P x -> Q x) ->
    forall t, TreeForall P t -> TreeForall Q t.
Proof.
 intros P Q Impl t Pt.
 induction Pt.
 - now constructor.
 - constructor; now auto.
Qed.

Lemma balance_Forall : forall P col a y b,
  TreeForall P a -> P y -> TreeForall P b -> TreeForall P (balance col a y b).
Proof.
  intros P col a y b Pa Py Pb.
  apply (balance_aux (fun '(col',t1,e,t2) t => col'=col/\t1=a/\e=y/\t2=b -> TreeForall P (t))).
  - (* もみほぐしその1 *)
    intros a' b' c d x y' z [Hcol [Ha [Hy Hb]]]. subst.
    inversion Pa. inversion H4. subst. constructor; [assumption | |].
    + now constructor.
    + now constructor.
  - (* もみほぐしその2 *)
    intros a' b' c d x y' z [Hcol [Ha [Hy Hb]]]. subst.
    inversion Pa. inversion H5. subst. constructor; [assumption | |].
    + now constructor.
    + now constructor.
  - (* もみほぐしその3 *)
    intros a' b' c d x y' z [Hcol [Ha [Hy Hb]]]. subst.
    inversion Pb. inversion H4. subst. constructor; [assumption | |].
    + now constructor.
    + now constructor.
  - (* もみほぐしその4 *)
    intros a' b' c d x y' z [Hcol [Ha [Hy Hb]]]. subst.
    inversion Pb. inversion H5. subst. constructor; [assumption | |].
    + now constructor.
    + now constructor.
  - (* もみほぐしが起きなかったとき *)
    intros col' a' y' b' [Hcol [Ha [Hy Hb]]]. subst. now constructor.
  - tauto.
Qed.

Lemma ins_Forall : forall P x t,
  TreeForall P t -> P x -> TreeForall P (ins x t).
Proof.
  intros P x t. apply ins_ind.
  - (* t = Eのとき *)
    intros _ _ _ Px. now constructor.
  - (* t = T col a y b で x < yのとき *)
    intros _ col a y b _ _ _ IHa Pt Px. inversion Pt. apply balance_Forall; now auto.
  - (* t = T col a y b で x > yのとき *)
    intros _ col a y b _ _ _ _ _ IHb Pt Px. inversion Pt. apply balance_Forall; now auto.
  - (* t = T col a y b で x = yのとき *)
    intros s col a y b Heq _ _ _ _ Pt Px. subst s. assumption.
Qed.

(**
     二分木の要素が対象順(symmetric order)で格納されているということを示す[Prop]。
     「対象順とは任意の与えられたノードの要素が、その左側の部分木の中のどの要素よりも大きく、
     右側の部分木のどの要素よりも小さい、という意味である」
 *)
Inductive Ordered : tree -> Prop :=
| OrderedE : Ordered E
| OrderedT : forall col t1 x t2, Ordered t1 -> Ordered t2 -> TreeForall (fun x1 => x1 < x) t1 -> TreeForall(fun x2 => x < x2) t2 -> Ordered (T col t1 x t2).

Lemma balance_Ordered : forall col a y b,
 Ordered a -> Ordered b ->
 TreeForall (fun x => x < y) a -> TreeForall (fun x => y < x) b ->
   Ordered (balance col a y b).
Proof.
  intros col a y b Orda Ordb Lt_ay Lt_yb.
  apply (balance_aux (fun '(col',a',y',b') t => col'=col/\a'=a/\y'=y/\b'=b -> Ordered t)).
  - (* もみほぐし 1 *)
    intros a11 a12 a2 b' e2 e1 y' [Hcol [Ha [Hy Hb]]]. subst.
    inversion Orda as [|col a1 x1' a2' Orda1 Orda2 Lt_a1 Lt_a2]. subst. clear Orda.
    inversion Orda1 as [|col a'' x' b'' Orda' Ordb' Lt_a' Lt_b']. subst. clear Orda1.
    inversion Lt_ay as [|col a1 x1' a2' Lt_x1 Lt_a1' Lt_a2']. subst. clear Lt_ay.
    constructor.
    + now constructor.
    + now constructor.
    + inversion Lt_a1. now constructor.
    + constructor; [assumption | assumption|].
      eapply TreeForall_impl; [|exact Lt_yb]. intros x. simpl.
      now apply Elem.Ord.lt_trans.
  - (* もみほぐし 2 *)
    intros a1 a21 a22 b' e1 e2 y' [Hcol [Ha [Hy Hb]]]. subst.
    inversion Orda as [|col a1' x1' a2 Orda1 Orda2 Lt_a1 Lt_a2]. subst. clear Orda.
    inversion Orda2 as [|col a'' x' b'' Orda' Ordb' Lt_a' Lt_b']. subst. clear Orda2.
    inversion Lt_ay as [|col a1' x1' a2' Lt_x1 Lt_a1' Lt_a2']. subst. clear Lt_ay.
    inversion Lt_a2 as [|col a21' e2' a22' Lt_e12 Lt_a21 Lt_a22]. subst. clear Lt_a2.
    inversion Lt_a2' as [|col a21' e2' a22' Lt_e1y Lt_a21' Lt_a22']. subst. clear Lt_a2'.
    constructor.
    + now constructor.
    + now constructor.
    + constructor; [assumption| |assumption].
      eapply TreeForall_impl; [|exact Lt_a1]. intros a1_x.
      simpl. intros Hlt. apply (Elem.Ord.lt_trans _ _ _ Hlt Lt_e12).
    + constructor; [assumption | assumption|].
      eapply TreeForall_impl; [|exact Lt_yb]. intros b_x. simpl.
      now apply Elem.Ord.lt_trans.
  - (* もみほぐし 3 *)
    intros a' b11 b12 b2 y' e2 e1 [Hcol [Ha [Hy Hb]]]. subst.
    inversion Ordb as [|col b1 e1' b2' Ordb1 Ordb2 Lt_b1e1 Lt_e1b2]. subst. clear Ordb.
    inversion Ordb1 as [|col b11' e2' b12' Ordb11 Ordb12 Lt_b11 Lt_b12]. subst. clear Ordb1.
    inversion Lt_yb as [|col b11' e1' b2' Lt_xe1 Lt_yb1 Lt_yb2]. subst. clear Lt_yb.
    inversion Lt_b1e1 as [|col b11' e2' b12' Lt_e2e1 Lt_b11e1 Lt_b12e1]. subst. clear Lt_b1e1.
    inversion Lt_yb1 as [|col b11' e2' b12' Lt_ye2 Lt_yb11 Lt_yb12]. subst. clear Lt_yb1.
    constructor.
    + now constructor.
    + now constructor.
    + constructor; [assumption| |assumption].
      eapply TreeForall_impl; [|exact Lt_ay]. intros a_x. simpl.
      intros Hlt. now apply (Elem.Ord.lt_trans _ y _).
    + constructor; [assumption | assumption|].
      eapply TreeForall_impl; [|exact Lt_e1b2]. intros x. simpl.
      now apply Elem.Ord.lt_trans.
  - (* もみほぐし 4 *)
    intros a' b1 b21 b22 y' e1 e2 [Hcol [Ha [Hy Hb]]]. subst.
    inversion Ordb as [|col b1' e1' b2' Ordb1 Ordb2 Lt_b1e1 Lt_e1b2]. subst. clear Ordb.
    inversion Ordb2 as [|col b21' e2' b22' Ordb21 Ordb22 Lt_b21 Lt_b22]. subst. clear Ordb2.
    inversion Lt_yb as [|col b11' e1' b2' Lt_ye1 Lt_yb1 Lt_yb2]. subst. clear Lt_yb.
    inversion Lt_e1b2 as [|col b21' e2' b22' Lt_e2e1 Lt_e1b21 Lt_e1b22]. subst. clear Lt_e1b2.
    inversion Lt_yb2 as [|col b21' e2' b22' Lt_ye2 Lt_yb21 Lt_yb22]. subst. clear Lt_yb2.
    constructor.
    + now constructor.
    + now constructor.
    + constructor; [assumption| |assumption].
      eapply TreeForall_impl; [|exact Lt_ay]. intros a_x. simpl.
      intros Hlt. now apply (Elem.Ord.lt_trans _ y _).
    + now constructor.
  - (* もみほぐし がおきない *)
    intros col' a' y' b' [Hcol [Ha [Hy Hb]]]. subst. now constructor.
  - tauto.
Qed.    

Lemma ins_Ordered : forall x t,
    Ordered t -> Ordered (ins x t).
Proof.
  intros x t. apply ins_ind.
  - (* t = E のとき *)
    intros _ _ Ordt. constructor; now constructor.
  - (* t = T col a y bで x < y のとき *)
    intros _ col a y b _ Hlt _ IHa Ordt.
    inversion Ordt.
    apply balance_Ordered; [now apply IHa| assumption| |assumption].
    now apply ins_Forall.
  - (* t = T col a y bで x > y のとき *)
    intros _ col a y b _ _ _ Hgt _ IHa Ordt.
    inversion Ordt.
    apply balance_Ordered; [assumption | now apply IHa | assumption | ].
    now apply ins_Forall.
  - (* t = T col a y bで x = y のとき *)
    intros s col a y b Heq Hgt _ Hlt _ Ordt. subst s. assumption.
Qed.

Theorem insert_Ordered : forall x t,
    Ordered t -> Ordered (insert x t).
Proof.
  intros x t Ordt. unfold insert.
  destruct (ins_Ordered x _ Ordt); now constructor.
Qed.

(**
 ** 演習 3.9

 重複のないソート済みリストから赤黒木へ変換する、型 [list Elem.T -> tree] の関数 [fromOrdList] を書いて見よう。
 その関数は O(n) 時間で実行できるはずだ。
 *)

Variable fromOrdListAux : nat -> list Elem.T -> nat -> (tree * list Elem.T).
Variable R : Set. (* 0以上の実数 *)
Variable floor : R -> nat.
Variable log2 : nat -> R.

Definition fromOrdList xs :=
  let n := List.length xs in
  let maxDepth := floor (log2 n) in
  fromOrdListAux n xs maxDepth.
