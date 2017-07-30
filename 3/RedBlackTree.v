Require Import Program Arith String List.
Require Import Recdef.
Open Scope string_scope.
Open Scope list_scope.

Require Import PFDS.common.Util.
Require Import PFDS.common.Ordered.
Require Import PFDS.common.Result.

Declare Module Elem : Ordered.

(**
 ** 赤黒木(Red Black Tree)

    #<img src="" />#
 *)

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