#!/bin/bash

logs="$@"

function generate_output_line {
    workload="$1"
    mode="$2"
    if [ -z "$logs" ]; then
        return
    fi
    throughputs=`sed -n "s,^\[step\] $workload $mode throughput \(.*\) ops/sec$,\1,p" $logs`
    if [ -z "$throughputs" ]; then
        return
    fi
    sorted_throughputs=`echo "$throughputs" | sort -n`
    min=`echo "$sorted_throughputs" | head -1`
    max=`echo "$sorted_throughputs" | tail -1`
    nthroughputs=`echo "$sorted_throughputs" | wc -l`
    median_index=$[ $nthroughputs / 2 + 1 ]
    median=`echo "$sorted_throughputs" | head -$median_index | tail -1`
    if [ $mode == "load" ]; then
        echo Load $median $min $max
    else
        echo $workload $median $min $max
    fi
    
}

workloads=("A" "Cuniform" "B" "C" "D" "F")

function generate_output_file {
    echo Workload  MedianThroughput  MinThroughput  MaxThroughput
    for workload in ${workloads[@]}; do
        if [ "$workload" == "A" ]; then
            generate_output_line "$workload" "load"
        fi
        generate_output_line "$workload" "run"
    done
}

generate_output_file
