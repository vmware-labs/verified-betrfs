#! /bin/bash

# Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
# SPDX-License-Identifier: BSD-2-Clause


RUNTIME=`dotnet --list-runtimes | grep 'Microsoft.NETCore.App' | head -n 1 | sed 's/.* \(.*\) .*/\1/'`

echo dotnet core runtime $RUNTIME >&2

echo "{\"runtimeOptions\": { \"framework\": { \"name\": \"Microsoft.NETCore.App\", \"version\": \"$RUNTIME\" } } }"
