#! /bin/bash

set -e

input=$1
output=$2

mkdir -p $output
opsfile=$output/opsfile

grep Ops $input | awk '{ print $6 }' > $opsfile
split --lines=14 $opsfile

mv xaa $output/seq_read_uncontended
mv xab $output/rand_read_uncontended
mv xac $output/seq_write_uncontended
mv xad $output/rand_write_uncontended

mv xae $output/seq_read_contended
mv xaf $output/rand_read_contended
mv xag $output/seq_write_contended
mv xah $output/rand_write_contended

mv xai $output/seq_read_io
mv xaj $output/rand_read_io
mv xak $output/seq_write_io
mv xal $output/rand_write_io
