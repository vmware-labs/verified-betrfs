#! /bin/bash

# Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
# SPDX-License-Identifier: BSD-2-Clause


echo "NOTE: using /noNLarith and /compile:0"
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
#set -x
cmd="$DIR/../.dafny/bin/dafny $@ /induction:1 /noNLarith /compile:0 /timeLimit:20"
# if you don't have unbuffer, apt-get install expect
# unbuffer convinces dafny to emit colored errors even when stdout is a pipe.
# stdbuf -o0 and --line-buffered are my belt-and-suspenders attempts to keep dafny
# output displayed as soon as it's available.
# first grep: Strip out garbage lines
# second grep: Highlight error lines to separate from related lines.
echo $cmd
unbuffer $cmd \
    | stdbuf -o0 egrep --line-buffered -v '(^\s*\(|anon|^Execution trace)' \
    | stdbuf -o0 egrep --color=always 'Error:|$'
