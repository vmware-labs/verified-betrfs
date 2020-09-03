#!/bin/bash

logs="$@"

operations=("insert" "readpositive" "readnegative" "remove")

function generate_output_line {
    operation="$1"
    if [ -z "$logs" ]; then
        return
    fi
    throughputs=`sed -n "s,^$operation	\(.*\)$,\1,p" $logs`
    if [ -z "$throughputs" ]; then
        return
    fi
    throughputs=$(for t in $throughputs; do python3 -c "print(64000000 / $t * 1000)"; done)
    sorted_throughputs=`echo "$throughputs" | sort -n`
    min=`echo "$sorted_throughputs" | head -1`
    max=`echo "$sorted_throughputs" | tail -1`
    nthroughputs=`echo "$sorted_throughputs" | wc -l`
    median_index=$[ $nthroughputs / 2 + 1 ]
    median=`echo "$sorted_throughputs" | head -$median_index | tail -1`
    echo $operation  $median $min $max
}

function generate_output_file {
    echo "phase  med min max"
    for operation in ${operations[@]}; do
        generate_output_line $operation 
    done
}

generate_output_file

