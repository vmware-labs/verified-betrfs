#! /bin/bash

# Copyright 2018-2021 VMware, Inc.
# SPDX-License-Identifier: BSD-2-Clause


# if a recent dotnet core is installed, run csc with the first sdk version found
# by running dotnet --list-sdks

set -e

SDK_VER=`dotnet --list-sdks | head -n 1 | sed 's/\(.*\) .*/\1/'`
DOTNET_DIR=`dotnet --list-sdks | head -n 1 | sed 's/.* \[\(.*\)\]/\1/'`
SDK_DIR="$DOTNET_DIR/$SDK_VER"

echo dotnet core $SDK_VER in $SDK_DIR

dotnet $SDK_DIR/Roslyn/bincore/csc.dll /r:$SDK_DIR/ref/netstandard.dll $@
