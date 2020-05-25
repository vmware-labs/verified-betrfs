#! /bin/bash

set -e
set -x

    

cd .dafny/dafny/
git fetch
if [ $1 ]; then
    ../../tools/checkout-dafny-commit.sh $1
else
    ../../tools/checkout-dafny-commit.sh
fi
git pull || true # don't try to pull if dafny pointer is to a specific commit, not a branch name
mono ../boogie/nuget.exe restore Source/Dafny.sln
msbuild /p:Configuration=Release Source/Dafny.sln
