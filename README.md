PFDSのアルゴリズムをCoqで書きたい

![イミュータブルデータ構造は遅いような気がしていたがそんなことはなかったぜ！](http://raw.github.o-in.dwango.co.jp/Yoshihiro-Imai/pfds_coq/images/PFDS_kinaba.png)

## ディレクトリ構成

```tree
.
├── common 章に依存しないコード
├── 2 第二章のコード
└── 3 第三章のコード
```


## 必要要件

[Coqのインストール方法](http://gist.github.o-in.dwango.co.jp/Yoshihiro-Imai/c9fc864f04e28c0299f72add23ad7fa8)

* coq = (version 8.6)


## ビルド方法

```console
./configure.sh
make
```


## ドキュメント

- 第二章
    - [2.2 二分探索木](http://pages.github.o-in.dwango.co.jp/Yoshihiro-Imai/pfds_coq/PFDS.2.BinaryTree.html)
- 第三章
    - [3.1 左偏ヒープ](http://pages.github.o-in.dwango.co.jp/Yoshihiro-Imai/pfds_coq/PFDS.3.LeftistHeap.html)
    - [3.2 二項ヒープ](http://pages.github.o-in.dwango.co.jp/Yoshihiro-Imai/pfds_coq/PFDS.3.BinomialHeap.html)
- [索引](http://pages.github.o-in.dwango.co.jp/Yoshihiro-Imai/pfds_coq/index.html)
