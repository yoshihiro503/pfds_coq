Require Import List Program Arith String.
Open Scope string_scope.
Open Scope list_scope.

Require Import PFDS.common.Ordered.
Require Import PFDS.common.Result.


Declare Module Elem : Ordered.

(**
   ** 二項木(Binomial Tree)
 *)

(**
   二項木は以下のように帰納的に定義される (p.30)
   - ランク [0] の二項木は 単一ノード
   - ランク [r+1] の二項木 はランク [r]の２つの二項木を [link]して作られる、
   このとき片方の木をもう片方の木の最左の子としてつなげる。
 *)
Inductive tree : Set :=
| Node : nat -> Elem.T -> list tree -> tree.

(**
   リンクするのはランクの等しい木だけ。
   引数の木は、上記の二項木の制約を満たすもののみを想定すれば良いっぽい。
   できる木は必ず子要素がランクの昇順に並んでいるはず
 *)
Definition link t1 t2 :=
  match (t1, t2) with
  | (Node r x1 c1, Node _ x2 c2) =>
    if Elem.leq_bool x1 x2 then
      Node (r+1) x1 (t2 :: c1)
    else
      Node (r+1) x2 (t1 :: c2)
  end.

(**
   ** 二項ヒープ(Binomial Heap)
 *)

(**
   二項木をランクに関して昇順に並べたリストとして二項ヒープを定義。
   ランクが同じ二項木は存在しないものとする。
 *)
Definition heap := list tree.

Definition rank t :=
  match t with
  | Node r _ _ => r
  end.

(**
   ヒープに[Elem.T]型の要素を１つだけ追加する[insert]関数の定義。(p.31)
   [insert]は要素数1の二項木を追加するというアルゴリズムで実現する。
 *)
Fixpoint insTree t heap :=
  match heap with
  | [] => [t]
  | t' :: ts =>
    if rank t <? rank t' then
      t :: ts
    else
      insTree(link t t') ts
  end.


