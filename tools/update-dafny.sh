#! /bin/bash

set -e
set -x

cd .dafny/dafny/
git fetch
../../tools/checkout-dafny-commit.sh
msbuild /p:Configuration=Release Source/Dafny.sln
