# Setting things up

Use this script to install necessary tools, including an appropriately-recent
version of `mono`. The script will also build a copy of Dafny in the local
.dafny/ dir (using the veribetrfs variant of Dafny with support for linear
types).

```
sudo tools/prep-environment.sh
```

You can run veribetrfs-dafny manuall with `tools/local-dafny.sh`.
The Makefile will use veribetrfs-dafny by default.

## Verify the software stack

Adjust -j# to exploit all of your cores.
```
make -j4 status
```

## Lightweight benchmarking

We have a very brief benchmark for a quick sanity check that everything is working. Note that you don't need to run verification before building and running the system.

```
make elf
./build/Veribetrfs --benchmark=random-queries
```

## YCSB

YCSB is a serious benchmark suite for production key-value stores.

The c++ ycsb benchmark library and rocksdb are vendored as a git submodule. Run

```
$ ./tools/update-submodules.sh
```

to initialise git submodules and to update the checkouts of the modules.

```
$ make build/VeribetrfsYcsb
```

builds the benchmark and all its dependencies (veribetrfs, rocsdb, the ycsb library, our ycsb library wrapper).

Our ycsb library wrapper is in `ycsb/wrappers`.

Some ycsb workload specifications are in `ycsb/*.spec`.

To run the benchmark, use

```
./build/VeribetrfsYcsb <workload_spec> <data_dir>
```

where `<data_dir>` should be an empty (or non-existing) directory that will contain the benchmark's files.

