#!/bin/sh
# Args: git-branch to check out
git fetch
git checkout $*
git pull
git rev-parse --abbrev-ref HEAD
tools/update-submodules.sh
tools/update-dafny.sh
rm -rf build/
make clean
