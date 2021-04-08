#! /bin/bash

# Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
# SPDX-License-Identifier: BSD-2-Clause

NONLINEAR_ARITH_ARG=/noNLarith
for arg in "$@"
do
  if [ ${arg: -4} == ".dfy" ]; then
    grep 'veribetrkv-dafny-directive:nonlinear' $arg > /dev/null && {
      echo "using nonlinear arithmetic"
      NONLINEAR_ARITH_ARG=
    }
  fi
done

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
set -x
$DIR/../.dafny/bin/dafny "$@" /trace /induction:1 $NONLINEAR_ARITH_ARG
