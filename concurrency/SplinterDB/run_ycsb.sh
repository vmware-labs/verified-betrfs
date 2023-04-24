#! /bin/bash

threads=14
memorysizes="4 20 100"
dbsize="240"
runs="ycsb_load ycsb_a ycsb_b ycsb_c ycsb_d ycsb_f ycsb_e"

set -e

filename=db

while getopts 'f:t:sh' opt; do
   case "$opt" in
      f)
         filename=$OPTARG
         ;;
      t)
         tracedir=$OPTARG
         ;;
      s)
         memorysizes="1 4 12"
         dbsize="30"
         runs="small_ycsb_load small_ycsb_a small_ycsb_b small_ycsb_c small_ycsb_d small_ycsb_f small_ycsb_e"
         ;;
      ?|h)
      echo "Usage: $(basename $0) [-f filename] -t tracedir"
      echo "filename is the location of the db file (may be large!)"
      echo "tracedir is the directory holding the YCSB traces to replay (mandatory)"
      exit 1
      ;;
   esac
done

if [ -z "$tracedir" ] || [ -z "$filename" ]; then
   echo "Usage: $(basename $0) [-f filename] -t tracedir"
   echo "filename is the location of the db file (may be large!)"
   echo "tracedir is the directory holding the YCSB traces to replay (mandatory)"
   exit 1
fi

rm -f $filename

# Run YCSB with 4GiB cache, then 20GiB cache, then 100GiB cache

# Unverified
./scripts/run_ycsb.py ycsb_results/unverified $runs --memory $memorysizes --trace_dir $tracedir --threads $threads --db_size $dbsize --config "--set-O_DIRECT --db-location $filename --set-hugetlb"
rm $filename

# IronSync
./scripts/run_ycsb.py ycsb_results/ironsync $runs --memory $memorysizes --trace_dir $tracedir --threads $threads --db_size $dbsize --config "--set-O_DIRECT --db-location $filename --set-hugetlb --ironsync"
rm $filename
