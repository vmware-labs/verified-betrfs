# Setting things up

## Automatic setup (Linux)

On Linux, use this script to install necessary tools, including an appropriately-recent
version of `mono`. The script will also build a copy of Dafny in the local
.dafny/ dir (using the veribetrfs variant of Dafny with support for linear
types).

```
sudo tools/prep-environment.sh
```

## Manual setup (Mac, Linux)

1. Install [Mono](https://www.mono-project.com/download/stable/).

2. Run

```
./tools/install-dafny.sh
```

This will install VeriBetrFS's [custom version of Dafny](https://github.com/secure-foundations/dafny) which includes our linear types extension.

3. Install Python dependencies for our build chain.

```
pip3 install toposort
```

# Running VeriBetrFS dafny

You can run veribetrfs-dafny manually with `tools/local-dafny.sh`.
The Makefile will use veribetrfs-dafny by default.

## Verify the software stack

Adjust -j# to exploit all of your cores.
```
make -j4 status
```

Expect this to take at least a couple of hours of CPU time.

## Lightweight benchmarking

We have a very brief benchmark for a quick sanity check that everything is working. Note that you don't need to run verification before building and running the system.

```
make elf
./build/Veribetrfs --benchmark=random-queries
```

## YCSB

YCSB is a serious benchmark suite for production key-value stores.

The C++ YCSB benchmark library and rocksdb are vendored as a git submodule. Run

```
$ ./tools/update-submodules.sh
```

to initialise git submodules and to update the checkouts of the modules. We also recommend
setting:

```
git config --global submodule.recurse true
```

This will ensure the submodules are updated when you do a git checkout.

Finally, to actually build the benchmark and all its dependencies (veribetrfs, rocsdb, the ycsb library, our ycsb library wrapper), run

```
$ make build/VeribetrfsYcsb
```

Our YCSB library wrapper is in `ycsb/wrappers`.

Some YCSB workload specifications are in `ycsb/*.spec`.

To run the benchmark, use

```
./build/VeribetrfsYcsb <workload_spec> <data_dir>
```

where `<data_dir>` should be an empty (or non-existing) directory that will contain the benchmark's files.
