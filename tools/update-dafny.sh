#! /bin/bash

set -e
set -x

cd .dafny/dafny/
git fetch
../../tools/checkout-dafny-commit.sh
mono ../boogie/nuget.exe restore Source/Dafny.sln
msbuild /p:Configuration=Release Source/Dafny.sln
