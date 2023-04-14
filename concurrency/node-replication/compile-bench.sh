#!/bin/bash

set -e

for n_replicas in 1 2 3 4; do
    make clean
    sed -i "s/\(NUM_REPLICA.*:= \).*;/\1${n_replicas};/" Constants.i.dfy
    make BundleVSpace.i.cpp || true
    # Needed until lseq_alloc_raw_hugetables compile issue is resolved.
    sed -i 's/^ *\(s = LinearExtern::lseq_alloc_raw_hugetables\)/\/\/ \1/' BundleVSpace.i.cpp
    make || true
    [[ -f "app" ]] && mv app app-${n_replicas}replicas
done

