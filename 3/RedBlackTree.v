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
(* TODO *)
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
 ** insertの定義
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

Lemma balance_Colored : forall col a y b col0 t1 e t2,
  (WellColored a /\ WellColored b) \/
    ((exists col_a a1 x a2, a = T col_a a1 x a2 /\ WellColored a1 /\ WellColored a2 /\
                            IsRootBlack a1 /\ IsRootBlack a2) /\ WellColored b) \/
    (WellColored a /\ (exists col_b b1 x b2, b = T col_b b1 x b2 /\ WellColored b1 /\
                                             WellColored b2 /\ IsRootBlack b1 /\ IsRootBlack b2)) ->
  balance col a y b = T col0 t1 e t2 ->
  WellColored t1 /\ WellColored t2.
Proof.
(*  
  intros col a y b col0 t1 e t2 HC Hbal.
  assert (WellColored a /\ WellColored b).
  - destruct HC as [HC|[HC|HC]].
    + assumption.
    + destruct HC as [HC Cb]. split; [|assumption].
      destruct HC as [col_a [a1 [x [a2 [Ha [Ca1 [Ca2 [Ba1 Ba2]]]]]]]].
      subst a. destruct col_a; now constructor.
    + destruct HC as [Ca HC]. split; [assumption|].
      destruct HC as [col_b [b1 [x [b2 [Hb [Cb1 [Cb2 [Bb1 Bb2]]]]]]]].
      subst b. destruct col_b; now constructor.
  - 
*)

  intros col a y b col0 t1 e t2 HC.
  apply (balance_aux (fun '(col', a', y', b') t => balance col' a' y' b' = t ->
                                                   col'=col/\a'=a/\y'=y/\b'=b ->
    t = T col0 t1 e t2 -> WellColored t1 /\ WellColored t2)).
  - (* もみほぐしが起きるとき その1 *)
    intros a' b' c' d' x' y' z' _ [Hcol [Ha [ Hz Hd]]] Heq. inversion Heq. subst.
    destruct HC as [[HCa HCb] |[[HCa HCb]| [HCa HCb]]].
    + inversion HCa. split; [|now constructor]. inversion H2. now constructor.
    + destruct HCa as [col_a [a1 [x [a2 [Heq2 [HCa1 [HCa2 [_ _]]]]]]]]. inversion Heq2. subst.
      split; [|now constructor]. inversion HCa1. now constructor.
    + now inversion HCa.
  - (* もみほぐしが起きるとき その2 *)
    intros a' b' c' d' x' y' z' _ [Hcol [Ha [ Hz Hd]]] Heq. inversion Heq. subst.
    destruct HC as [[HCa HCb] |[[HCa HCb]| [HCa HCb]]].
    + inversion HCa. inversion H3. split; now constructor.
    + destruct HCa as [col_a [a1 [x [a2 [Heq2 [HCa1 [HCa2 [_ _]]]]]]]]. inversion Heq2. subst.
      inversion HCa2. split; now constructor.
    + now inversion HCa.
  - (* もみほぐしが起きるとき その3 *)
    intros a' b' c' d' x' y' z' _ [Hcol [Ha [ Hz Hd]]] Heq. inversion Heq. subst.
    destruct HC as [[HCa HCb] |[[HCa HCb]| [HCa HCb]]].
    + inversion HCb. inversion H2. split; now constructor.
    + now inversion HCb.
    + destruct HCb as [col_b [b1 [x [b2 [Heq2 [HCb1 [HCb2 [_ _]]]]]]]]. inversion Heq2. subst.
      inversion HCb1. split; now constructor.
  - (* もみほぐしが起きるとき その4 *)
    intros a' b' c' d' x' y' z' _ [Hcol [Ha [ Hz Hd]]] Heq. inversion Heq. subst.
    destruct HC as [[HCa HCb] |[[HCa HCb]| [HCa HCb]]].
    + inversion HCb. inversion H3. split; now constructor.
    + now inversion HCb.
    + destruct HCb as [col_b [b1 [x [b2 [Heq2 [HCb1 [HCb2 [_ _]]]]]]]]. inversion Heq2. subst.
      inversion HCb2. split; now constructor.
  - (* もみほぐしが起きないとき *)
    intros col1 t1' e' t2' Heq [Hcol1 [Ht1' [He' Ht2']]] Ht. inversion Ht. subst.
    destruct HC as [HC | [[HCa HCb]| [HCa HCb]]].
    + assumption.
    + split; [|assumption].
      destruct HCa as [col_a [a1 [x [a2 [Heq2 [HCa1 [HCa2 [Ba1 Ba2]]]]]]]]. subst.
      destruct col_a; now constructor.
    + split; [assumption|].
      destruct HCb as [col_b [b1 [x [b2 [Heq2 [HCb1 [HCb2 [Bb1 Bb2]]]]]]]]. subst.
      destruct col_b; now constructor.
  - reflexivity.
  - tauto.
Qed.

(*Lemma ins_Colored : forall x t col t1 e t2,
  WellColored t ->
  ins x t = T col t1 e t2 -> WellColored t1 /\ WellColored t2.
Proof.
  intros x t. apply ins_ind.
  - (* t = E *)
    intros _ _ col t1 e t2 HC Heq. inversion Heq. now split.
  - (* t = T col a y b で x < y *)
    intros _ col a y b _ _ _ IHa col0 t1 e t2 HC Heq.
    cut (WellColored a); [intros HCa| now inversion HC].
    cut (WellColored b); [intros HCb| now inversion HC].
    eapply balance_Colored; [| exact Heq].
    case_eq (ins x a); [left; now split|].
    intros c t1' e' t2' Hins_a.
    destruct (IHa _ _ _ _ HCa Hins_a) as [IHa1 IHa2].
    destruct c.
    + (* ins x a の結果が赤のとき *)
      destruct col.
        (* 元の木の根が赤のとき *)
      * inversion HC as [| a' y' b' _ _ Ba Bb |].
        right; left. split; [|assumption]. exists 赤, t1', e', t2'.
        edestruct (ins_color_changed a x e' t1' t2' HCa Ba Hins_a) as [Bt1' Bt2'].
        tauto.
        (* 元の木の根が黒のとき *)
      * rewrite Hins_a in Heq.
        { destruct t1' as [|col1 t11 e1 t12].
          - destruct t2' as [|col2 t21 e2 t22]; [left; now split; [constructor|]|].
            destruct col2; [right; left|right; left].
            + split; [| assumption]. exists 赤, E, e', (T 赤 t21 e t22).
              unfold balance in Heq.
        split; [|split; [|split]]; try now auto.
        { split.
          - destruct t1'; [now constructor|].
            destruct c; [|now constructor].
            

        
    + (* ins x a の結果が黒のとき *)
Qed.
*)

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
