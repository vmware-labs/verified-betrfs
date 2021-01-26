#!/bin/bash

set -e
set -x

cd .dafny/dafny/
git fetch
../../tools/checkout-dafny-commit.sh "$@"
git pull || true # don't try to pull if dafny pointer is to a specific commit, not a branch name

cd ..
dotnet build dafny/Source/Dafny.sln
