#!/bin/bash

set -x

dotnet --list-sdks | grep '^3.1'
if [ $? -ne 0 ]; then
  echo "You must install .NET Core 3.1: https://dotnet.microsoft.com/download"
  exit 1
fi

set -e

mkdir .dafny
cd .dafny

git clone https://github.com/secure-foundations/dafny.git --recurse-submodules
cd dafny
../../tools/checkout-dafny-commit.sh "$@"

cd ..
dotnet build dafny/Source/Dafny.sln

# XXX add this symlink for backwards compatability with our current Makefile
# which is written to be compatabile with dafny 2. TODO clean this up after
# we're comfortable only using dafny 3.
cd dafny/Binaries
ln -s ../Scripts/dafny dafny

cd ../..
if [ `uname` == "Darwin" ]; then
  make -C dafny z3-mac
elif [ `uname` == "Linux" ]; then
  make -C dafny z3-ubuntu
else
  echo "error: unknown host os"
  exit 1
fi
