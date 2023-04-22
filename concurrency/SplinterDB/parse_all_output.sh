#! /bin/bash

for i in 0 1 2 3 4
do
   mkdir -p micro_run_$i/unverified_parsed
   mkdir -p micro_run_$i/ironsync_parsed
   ./parse_output.sh micro_run_$i/unverified micro_run_$i/unverified_parsed
   ./parse_output.sh micro_run_$i/ironsync micro_run_$i/ironsync_parsed
done

mkdir -p micro_results
mkdir -p micro_results/unverified
mkdir -p micro_results/ironsync

for scen in uncontended contended io
do
   for pattern in seq rand
   do
      for access in read write
      do
         filename="${pattern}_${access}_${scen}"
         awk '{a[FNR]+=$1;b[FNR]++;}END{for(i=1;i<=FNR;i++)printf "%d\n", a[i]/b[i];}' micro_run_*/unverified_parsed/$filename > micro_results/unverified/$filename
         nl -n ln -w 7 micro_results/unverified/$filename > micro_results/unverified/temp
         mv micro_results/unverified/temp micro_results/unverified/$filename
         sed -i '1s/^/threads throughput\n/' micro_results/unverified/$filename

         awk '{a[FNR]+=$1;b[FNR]++;}END{for(i=1;i<=FNR;i++)printf "%d\n", a[i]/b[i];}' micro_run_*/ironsync_parsed/$filename > micro_results/ironsync/$filename
         nl -n ln -w 7 micro_results/ironsync/$filename > micro_results/ironsync/temp
         mv micro_results/ironsync/temp micro_results/ironsync/$filename
         sed -i '1s/^/threads throughput\n/' micro_results/ironsync/$filename
      done
   done
done
