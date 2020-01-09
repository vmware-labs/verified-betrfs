#! /bin/bash

set -e

blu=$'\e[1;34m'
yel=$'\e[1;33m'
end=$'\e[0m'

echo "NOTE: ${blu}if this fails, you may need to ./tools/update-submodules.sh${end}"

set -x

make build/VeribetrfsYcsb

set +x

echo "${yel}== workload A ==${end}"
./build/VeribetrfsYcsb ycsb/workloada-onefield.spec

echo "${yel}== workload B ==${end}"
./build/VeribetrfsYcsb ycsb/workloadb-onefield.spec

echo "${yel}== workload C ==${end}"
./build/VeribetrfsYcsb ycsb/workloadc-onefield.spec

echo "`tput op`"
