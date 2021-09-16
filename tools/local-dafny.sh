#! /bin/bash

# Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
# SPDX-License-Identifier: BSD-2-Clause


echo "NOTE: using /noNLarith and /compile:0"
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
set -x
$DIR/../.dafny/bin/dafny "$@" /induction:1 /noNLarith /compile:0 /timeLimit:20
