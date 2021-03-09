#!/bin/bash

# Copyright 2018-2021 VMware, Inc.
# SPDX-License-Identifier: BSD-2-Clause


while getopts ":t:p:f:h:d:" opt; do
  case $opt in
    t) timelimit="$OPTARG" ;;
    p) proc="$OPTARG" ;;
    f) file="$OPTARG" ;;
    d) display="$OPTARG" ;;

    \?) echo "Invalid option -$OPTARG" >&2 ;;
  esac
done

if [ -z "$timelimit" ] || [ -z "$proc" ] || [ -z "$file" ]; then
    echo "tools/profile.sh -t timelimit -p procname -f filename"
    echo 'Missing -t or -p or -f' >&2
    exit 1
fi

addon=""
if [ ! -z "$display" ]; then
    addon=$(echo --show "$display")
fi

python3 tools/dafny-profile.py $timelimit Impl\*$proc\* $file $addon --dafny=./.dafny/bin/dafny
