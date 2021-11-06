#!/bin/bash

set -e

for n_replicas in 1 2 4; do
    make clean
    sed -i "s/\(NUM_REPLICA.*:= \).*;/\1${n_replicas};/" Constants.i.dfy
    make || true
    [[ -f "app" ]] && mv app app-${n_replicas}replicas
done

