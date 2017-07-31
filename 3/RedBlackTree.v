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

(**
 *** tree型の値が赤黒木となっているかという述語

 - ここでいうLengthは経路に含まれる黒ノードの数(赤黒木の全ての経路で黒ノードの数は同じ)
 - treeのElem.Tの順序については何も言っていない
 *)

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
