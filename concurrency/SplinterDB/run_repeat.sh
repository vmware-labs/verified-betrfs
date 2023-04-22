#! /bin/bash

set -e

filename=$1

for i in 0 1 2 3 4
do
   mkdir -p micro_run_$i
   echo "Running microbenchmark on unverified, run $i"
   stdbuf -i0 -o0 -e0 numactl -N 0 -m 0 ./bin/driver_test cache_test --perf --db-location /dev/nvme0n1 --set-O_DIRECT --set-hugetlb --cache-capacity-gib 4 > micro_run_$i/unverified
   echo "Running microbenchmark on IronSync, run $i"
   stdbuf -i0 -o0 -e0 numactl -N 0 -m 0 ./bin/veri_driver_test cache_test --perf --db-location /dev/nvme0n1 --set-O_DIRECT --set-hugetlb --cache-capacity-gib 4 > micro_run_$i/ironsync
done
