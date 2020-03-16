#! /bin/bash

set -e

blu=$'\e[1;34m'
yel=$'\e[1;33m'
end=$'\e[0m'

echo "NOTE: ${blu}if this fails, you may need to ./tools/update-submodules.sh${end}"

set -x

make -j 4 build/VeribetrfsYcsb

set +x

rm -R /tmp/veriexperiments || true
mkdir /tmp/veriexperiments

echo "${yel}== workload A ==${end}"
./build/VeribetrfsYcsb ycsb/workloada-onefield.spec /tmp/veriexperiments --veribetrkv
./build/RocksYcsb ycsb/workloada-onefield.spec /tmp/veriexperiments --rocks

echo "${yel}== workload B ==${end}"
./build/VeribetrfsYcsb ycsb/workloadb-onefield.spec /tmp/veriexperiments --veribetrkv
./build/RocksYcsb ycsb/workloadb-onefield.spec /tmp/veriexperiments --rocks

echo "${yel}== workload C ==${end}"
./build/VeribetrfsYcsb ycsb/workloadc-onefield.spec /tmp/veriexperiments --veribetrkv
./build/RocksYcsb ycsb/workloadc-onefield.spec /tmp/veriexperiments --rocks

echo "`tput op`"
