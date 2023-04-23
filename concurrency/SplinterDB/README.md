![SplinterDB Project Logo](docs/images/splinterDB-logo.png)

## What is SplinterDB?
SplinterDB is a key-value store designed for high performance on fast storage devices.

See
> Alexander Conway, Abhishek Gupta, Vijay Chidambaram, Martin Farach-Colton, Richard P. Spillane, Amy Tai, Rob Johnson:
[SplinterDB: Closing the Bandwidth Gap for NVMe Key-Value Stores](https://www.usenix.org/conference/atc20/presentation/conway). USENIX Annual Technical Conference 2020: 49-63

## SplinterDB with IronSync Cache

This version of SplinterDB can be run with a verified cache module. This module is linked into the test harbess via `./bin/veri_driver_test`, and the original unverified cache is linked via `./bin/driver_test`.

## How to Set Up and Build SplinterDB

SplinterDB requires libaio and libxxhash, and the build is known to work with clang-13. The microbenchmark uses numactl to restrict to a single NUMA node, and coreutils to write to output files without buffering.

The following commands download these prerequisites and build SplinterDB. Note that the first call to make fails spurriously, but the second will succeed.

```shell
$ sudo apt update -y
$ sudo apt install -y libaio-dev libxxhash-dev clang-13 numactl coreutils
$ make
$ make
```

## Set up Huge Page Support

The benchmarks are designed to run with huge pages enabled and allocated. In particular, the IronSync cache has this support hardcoded. To see the number of allocated huge pages, look at `/proc/meminfo/` or run

```shell
$ cat /proc/sys/vm/nr_hugepages
```

The YCSB benchmark requires up to 100GiB of huge-page memory, and the microbenchmark requires about 4GiB of huge-page memory to reside on a single NUMA node. Thus, with a small amount of extra buffer memory, the number of huge pages required is 100GiB * 1.125 / 2MiB = 57600. To allocate this run as root:

```shell
# echo 57600 > /proc/sys/vm/nr_hugepages
```

## Run the microbenchmark

The microbenchmark can be run as follows:

```shell
$ ./run_microbenchmark.sh -f dbfilename
```

`dbfilename` is the file that SplinterDB will store its data in. By default this is file called `db` in the local directory. CAUTION: This script deletes this file!

The microbenchmark runs 5 times on each system and the raw output for run i is stored in `micro_run_i`. Average throughput results are saved in `micro_results`. Each microbenchmark run takes approximately 1 hour with 2Ghz CPUs and an Intel 905P Optane SSD, so the full benchmark runs in about 10 hours.

This benchmark can be scaled down by editing `PERF_OPS` on `tests/cache_test.c:925`, and can scale to fewer threads by editing `PERF_THREADS`. If `PERF_THREADS` is changed, then `parse_output.sh:12` needs to be changed as well.

## Run the YCSB macrobenchmark

The YCSB benchmark is run by replaying YCSB operation traces. The traces can be downloaded from https://zenodo.org/record/7857018, and are 38GiB compressed and 110GiB uncompressed. The traces must be uncompressed and the directory holding the traces must be given as an argument to the script. Each run first loads a trace into memory and populates its values with random data.

# Requirements

This benchmark is very resource-intensive. Each trace while in memory consumes ~90GiB of memory in addition to the memory consumed by the benchmark itself. The largest cache size used is 100GiB, so almost 200GiB of system memory will be used by that run. The database file used is 240GiB in size. This benchmark is run with 14 threads.

A smaller version can be run by using `small_ycsb_traces.tar.gz`. To run this benchmark use the `-s` flag.

The benchmark script can be edited to, for example, exclude the 100GiB run by changing the value of `memorysizes` from `4 20 100` to `4 20`.

The benchmark can be run as follows:
```shell
$ ./run_ycsb.sh [-f dbfilename] -t tracedir [-s]
```

`dbfilename` is the file that SplinterDB will store its data in. By default this is file called `db` in the local directory. CAUTION: This script deletes this file! `tracedir` must point to the directory holding the trace files. `-s` uses smaller parameters for the memory sizes and db file size intended for use with the small traces.

The default version of the YCSB benchmark replays the traces on each system first with 4GiB cache, then 20GiB, then 100GiB. The results are stored in `ycsb_results`. The topline throughput numbers for each run are stored in files with names like `ycsb_results/unverified/results_value_100-thr_14-mem_4GiB-2023_04_21_16:22.csv`.
