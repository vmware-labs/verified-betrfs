#! /bin/bash

set -e

filename=db

while getopts 'f:h' opt; do
   case "$opt" in
      f)
         filename=$OPTARG
         ;;
      ?|h)
      echo "Usage: $(basename $0) [-f filename]"
      exit 1
      ;;
   esac
done

rm -f $filename

./run_repeat.sh $filename
./parse_all_output.sh
