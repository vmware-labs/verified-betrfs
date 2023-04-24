#! /bin/bash

set -e

filename=$1

if [ -z "$filename" ]; then
   echo "Invalid filename\n"
   exit
fi

for i in 0 1 2 3 4
do
   mkdir -p micro_run_$i
   echo "Running microbenchmark on unverified, run $i"
   stdbuf -i0 -o0 -e0 numactl -N 0 -m 0 ./bin/driver_test cache_test --perf --db-location $filename --set-O_DIRECT --set-hugetlb --cache-capacity-gib 4 > micro_run_$i/unverified
   rm $1
   echo "Running microbenchmark on IronSync, run $i"
   stdbuf -i0 -o0 -e0 numactl -N 0 -m 0 ./bin/veri_driver_test cache_test --perf --db-location $filename --set-O_DIRECT --set-hugetlb --cache-capacity-gib 4 > micro_run_$i/ironsync
   rm $1
done
