Require Import Program Arith String List.
Require Import Recdef.
Open Scope string_scope.
Open Scope list_scope.

Require Import PFDS.common.Util.
Require Import PFDS.common.Ordered.
Require Import PFDS.common.Result.


Declare Module Elem : Ordered.
Import Elem.Op.

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

Definition rank t :=
  match t with
  | Node r _ _ => r
  end.

(**
   *** 二項木の具体例
   二項木の具体例は以下の通り
   - ランク [0] : [Tree 0 x []]
   - ランク [1] : [Tree 1 y [(Tree 0 x [])]]
   - ランク [2] : [Tree 2 z [(Tree 1 y [(Tree 0 x [])]); (Tree 0 p [])]]
   (要素の数はランク[r]に従ってちょうど [2^r] 個となる)
 *)

(**
   *** [link] 関数の実装
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

Inductive BinomialTree : tree -> Prop :=
| BT_O: forall x, BinomialTree (Node 0 x [])
| BT_S: forall r t1 t2, BinomialTree t1 -> BinomialTree t2 -> rank t1 = r -> rank t2 = r -> BinomialTree (link t1 t2)
.

(**
   ** 二項ヒープ(Binomial Heap)
 *)

(**
   二項木をランクに関して昇順に並べたリストとして二項ヒープを定義。
   ランクが同じ二項木は存在しないものとする。
 *)
Definition heap := list tree.

(*TODOソート済みと重複無しも
Definition BinomialHeap ts : Prop := List.Forall BinomialTree ts.
*)

(**
   *** [insert] の実装
   ヒープに[Elem.T]型の要素を１つだけ追加する[insert]関数の定義。(p.31)
   [insert]は要素数1の二項木を追加するというアルゴリズムで実現する。
 *)
Fixpoint insTree t heap :=
  match heap with
  | [] => [t]
  | t' :: ts =>
    if (rank t <? rank t')%nat then
      t :: ts
    else
      insTree(link t t') ts
  end.

Definition insert x heap := insTree (Node 0 x []) heap.

(**
   *** [merge] の実装
 *)
Function merge ts1_ts2 {measure (pair_size (@List.length tree) (@List.length tree)) ts1_ts2} :=
  match (ts1_ts2) with
  | (ts1, []) => ts1
  | ([], ts2) => ts2
  | (t1 :: ts1' as ts1, t2 :: ts2' as ts2) =>
    if (rank t1 <? rank t2)%nat then
      t1 :: merge (ts1', ts2)
    else if (rank t2 <? rank t1)%nat then
      t2 :: merge (ts1, ts2')
    else
      insTree (link t1 t2) (merge (ts1', ts2'))
  end.
Proof.
  - simpl. now auto with arith.
  - simpl. now auto with arith.
  - simpl. now auto with arith.
Defined.

(**
   *** [findMin], [deleteMin]の定義
   *)

(**
   二項木から根っこの値をとる関数。この木の中に含まれる最小の値が取れるはず。
 *)
Definition root tree : Elem.T :=
  let '(Node _ x _) := tree in x.

(**
   ヒープから最小のroot値を持つ木を抜き出して、その木と残ったヒープを組みで返す。
   ヒープがからの場合を想定して[Result]型を返す
   [map]と[fold]でもかける気がするが教科書に合わせて再帰で書いた。
 *)
Fixpoint removeMinTree (h: heap) : Result (tree * heap) :=
  match h with
  | [] => Error "empty"
  | [t] => Ok (t, [])
  | t :: ts =>
    removeMinTree ts >>= fun t'_ts' =>
    let '(t', ts') := t'_ts' in
    if root t <=? root t' then
      ret(t, ts)
    else
      ret(t', t::ts')
  end.

(**
   ヒープに含まれる最小のElem.Tの値を返す
 *)
Definition findMin ts : Result(Elem.T) :=
  removeMinTree ts >>= fun '(t, _) =>
  Ok (root t).

(**
   二項木の子要素[ts1]は二項ヒープとなっているはずなので、mergeできる。
 *)
Definition deleteMin ts :=
  removeMinTree ts >>= fun '(Node _ x ts1, ts2) =>
  Ok (merge(List.rev ts1, ts2)).

(**
 ** 演習問題3.5
   [removeMinTree]の呼び出しを経由せず、findMinを直接的に定義してみよう
 *)
Definition findMin' ts :=
  ts
  |> map root
  |> reduce Elem.min
.

Lemma findMin'_correct_aux: forall t0 ts,
    Ok (fold_right Elem.min (root t0) (map root ts)) =
    (removeMinTree ((ts ++ [t0])%list) >>= fun '(tx, _) => Ok (root tx)).
Proof.
 induction ts.
 - now simpl.
 - simpl. revert IHts. case_eq (removeMinTree (ts ++ [t0])%list); [|discriminate].
   intros s_ss. destruct s_ss as [s ss]. simpl. intros eq IH. injection IH. intros IH'.
   destruct (Elem.leq_dec (root a) (root s)).
   + rewrite IH'. rewrite (Elem.min_l _ _ l). now destruct (ts ++ [t0])%list; simpl.
   + rewrite IH'. rewrite Elem.min_r; [| now apply Elem.lt_le_incl, Elem.not_le_lt].
     now destruct (ts ++ [t0])%list; simpl.
Qed.

Theorem findMin'_correct: forall ts,
  findMin' ts = findMin ts.
Proof.
 destruct ts.
 - now auto.
 - unfold findMin, findMin', pipeline, reduce, reduce_right.
   (* t::ts = us++[u] となるような us, uが存在する *)
   cut (exists u us, t :: ts = (us ++ [u])%list).
   + intros Exu. destruct Exu as [u Exus]. destruct Exus as [us eq]. rewrite eq at 2.
     simpl. rewrite <- findMin'_correct_aux.
     f_equal. apply Util.fold_right_cons_tail.
     * apply Elem.min_assoc.
     * apply Elem.min_comm.
     * rewrite <- map_cons. rewrite eq. now rewrite map_app.
   + destruct (@List.exists_last tree (t::ts)) as [us Exu]; [discriminate|].
     destruct Exu as [u  eq]. now exists u, us.
Qed.

(**
 ** 演習問題3.6

    https://dwango.slack.com/archives/C0CJRPYU8/p1501238725206210

    treeの代わりにheapでrankを持ったらどうなるかっていうこと

    (treeのノードで持つ代わりに,heapの中で [(rank, tree)] のタプルリストみたいにして持つようにする。)
<<
    link: (rank * tree) -> (rank * tree) -> (rank * tree) のような型になる
    insTree: (rank * tree) -> heap -> heap
    merge : heap -> heap -> heap だから型は変わらない。
>>
    removeMinTree とか findMin とかはもうrank関係ないからこのままで。

    link, insTree, insert, mergeの実装を修正すればよさそう
 *)


(**
 ** 演習問題3.7

    https://dwango.slack.com/archives/C0CJRPYU8/p1501240301621876

    例えばinsertはScalaで次のような感じかな:
<<
    def insert (x: Elem.T, h: Heap) = {
      h match {
        case E => NE(x, H.singleton(x))
        case NE(m, ih) =>
          NE(min(m, x), H.insert(x, ih))
      }
    }
>>
    mergeなども同様にできそう。
    
    `NE(x, ih)` で `ih`の中に `x` を含まない流派 (a.mutake派)と 含む派 (y.oshihiro503派) がある。(上記は含む派)
 *)

(**
 ** 3.2節まとめ

<<
insert : O(log n)
merge: O(log n)
findMin: O(log n)
deleteMin: O(log n)
>>

ただし、ちょっとした拡張でfindMinはO(1)にできる (ExplicitMinファンクタ)
 *)
