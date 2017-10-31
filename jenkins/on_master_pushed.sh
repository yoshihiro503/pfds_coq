#!/bin/sh
set -eux
export COQBIN=/Users/yoshihiro_imai/.opam/system/bin/
export PATH=$COQBIN:$PATH
./configure.sh
make clean
make -j
make -j html
echo 'GITHUB Pagesにデプロイ'
#git subtree push --prefix html origin gh-pages
cp -r html html-$BUILD_NUMBER
git clone -b gh-pages git@github.o-in.dwango.co.jp:Yoshihiro-Imai/pfds_coq.git gh-pages
rm -rf gh-pages/*
mv html-$BUILD_NUMBER/* gh-pages/
cd gh-pages/
git add .
git diff-index --quiet HEAD || git commit -am "by the jenkins build $BUILD_NUMBER: $BUILD_URL"
git push origin gh-pages
