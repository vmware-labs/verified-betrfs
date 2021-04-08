#! /bin/bash

# Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
# SPDX-License-Identifier: BSD-2-Clause


echo "NOTE: this will use the /noNLarith flag! Don't use this if you're working on a file where NLarith is allowed in the Makefile"
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
set -x
$DIR/../.dafny/bin/dafny "$@" /trace /induction:1 /noNLarith
