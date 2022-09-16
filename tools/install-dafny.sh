#! /bin/bash

# Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
# SPDX-License-Identifier: BSD-2-Clause


set -x

# dotnet-5.0 isn't available for ubuntu 22.04, so you have to install
# the no-longer-supported binaries manually from
# https://dotnet.microsoft.com/en-us/download/dotnet/thank-you/sdk-5.0.408-linux-x64-binariesp
# and then point paths at it when running .net stuff. :v/
# Here's jonh's hack:
export DOTNET_ROOT=$HOME/dotnet5-manual
export PATH=$PATH:$HOME/dotnet5-manual

dotnet --list-sdks | grep '^5.0'
if [ $? -ne 0 ]; then
  echo "You must install .NET Core 5.0: https://dotnet.microsoft.com/download"
  exit 1
fi

set -e

mkdir .dafny
cd .dafny

git clone https://github.com/secure-foundations/dafny.git
cd dafny
../../tools/checkout-dafny-commit.sh
make exe
cd ..

if [ `uname` == "Darwin" ]; then
    wget https://github.com/Z3Prover/z3/releases/download/Z3-4.8.5/z3-4.8.5-x64-osx-10.14.2.zip
    unzip z3-4.8.5-x64-osx-10.14.2.zip
    cp -r z3-4.8.5-x64-osx-10.14.2 dafny/Binaries/z3/
elif [ `uname` == "Linux" ]; then
    wget https://github.com/Z3Prover/z3/releases/download/Z3-4.8.5/z3-4.8.5-x64-ubuntu-16.04.zip
    unzip z3-4.8.5-x64-ubuntu-16.04.zip
    cp -r z3-4.8.5-x64-ubuntu-16.04 dafny/Binaries/z3/
fi

mkdir bin
echo "#! /bin/bash" > bin/dafny
echo "`pwd`/dafny/Scripts/dafny \"\$@\"" >> bin/dafny
chmod +x bin/dafny

## This is needed in case you want to call the Boogie binary directly.
## See the documentation: https://github.com/dafny-lang/dafny/blob/master/INSTALL.md
#rm -f boogie/Binaries/z3.exe
#cp dafny/Binaries/z3/bin/z3 boogie/Binaries/z3.exe
