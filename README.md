PFDSのアルゴリズムをCoqで書きたい

> 「イミュータブルデータ構造は遅いような気がしていたがそんなことはなかったぜ！」
[20分でわかるPurely FunctionalData Structures](http://www.kmonos.net/pub/Presen/PFDS.pdf)より

## ディレクトリ構成

```tree
.
├── common 章に依存しないコード
├── 2 第二章のコード
├── 3 第三章のコード
└── 5 第五章のコード
```


## 必要要件

[Coqのインストール方法](https://employment.en-japan.com/engineerhub/entry/2018/08/10/110000)

* coq = (version 8.6)


## ビルド方法

```console
./configure.sh
make
```


## ドキュメント

- 第二章
    - [2.2 二分探索木](http://yoshihiro503.github.io/pfds_coq/PFDS.2.BinaryTree.html)
- 第三章
    - [3.1 左偏ヒープ](http://yoshihiro503.github.io/pfds_coq/PFDS.3.LeftistHeap.html)
    - [3.2 二項ヒープ](http://yoshihiro503.github.io/pfds_coq/PFDS.3.BinomialHeap.html)
- [索引](http://yoshihiro503.github.io/pfds_coq/index.html)
