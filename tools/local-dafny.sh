#! /bin/bash

# Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
# SPDX-License-Identifier: BSD-2-Clause


echo "NOTE: this will use the /noNLarith flag! If you're working on a file where nonlinear arith is allowed use tools/local-dafny-nonlinear.sh"
echo "NOTE: since it's okay to park in the middle of the street with my blinkers on, jonh added /compile:0"
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
set -x
$DIR/../.dafny/bin/dafny "$@" /induction:1 /noNLarith /compile:0
