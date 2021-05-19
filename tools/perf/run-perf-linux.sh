#! /bin/bash

# Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
# SPDX-License-Identifier: BSD-2-Clause

# usage ./tools/perf/run-perf-linux.sh 1000 --benchmark=random-inserts

frequency=$1
shift

make CC=clang++ CCFLAGS="-g -fno-omit-frame-pointer" build/Veribetrfs

echo "==== starting benchmark ===="
echo "flags: $@"

./build/Veribetrfs $@ &
PID=$!
read -n 1 -s -r -p "Press any key to start recording"
perf record -p $PID --call-graph=dwarf,4096 -F$frequency &
PERF_PID=$!
sleep 1
read -n 1 -s -r -p "Press any key to stop recording"

set +e
kill $PID
sleep 2

echo "==== starting benchmark ===="

tmux \
  new-session  "perf report -g graph,0.1,callee,function,percent" \; \
  split-window "echo \"The upper pane is perf with callee trees, this is with caller trees. In tmux, use C-b Up and C-b Down to switch panes. If perf is crashing, try with a shorter trace.\"; read -n 1 -s -r -p \"Press any key to start loading this pane\"; perf report -g graph,0.4,caller,function,percent" \; \
  attach \;

