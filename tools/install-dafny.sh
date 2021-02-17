#! /bin/bash

set -x

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
