# Verified BetrFS

Verified BetrFS (VeriBetrFS) is a verified file system based on the design of [BetrFS](http://betrfs.org).

VeriBetrFS is implemented in [dafny](https://github.com/dafny-lang/dafny), which supports specifying and proving functional correctness.

VeriBetrFS uses the [IronFleet](https://www.microsoft.com/en-us/research/publication/ironfleet-proving-practical-distributed-systems-correct/) methodology to prove strong crash-safety guarantees.

# Publications

[Storage Systems are Distributed Systems (So Verify Them That Way!)](https://www.usenix.org/conference/osdi20/presentation/hance).  Travis Hance, Andrea Lattuada, Chris Hawblitzel, Jon Howell, Rob Johnson, and Bryan Parno. OSDI 2020.

# Current status

Like BetrFS, VeriBetrFS implements a file system on top of a B^e-tree-based key-value store.

VeriBetrFS currently includes a verified key-value store.

On-going work is focused on extending the key-value store to support cloning and to build the file-system layer.

# Setting things up

## Automatic setup (Linux)

On Linux, use this script to install necessary tools, including an appropriately-recent
version of .NET. The script will also build a copy of Dafny in the local
.dafny/ dir (using the veribetrfs variant of Dafny with support for linear
types).

```
sudo ./tools/prep-environment.sh
./tools/install-dafny.sh
```

## Manual setup (Mac, Linux)

1. Install [.NET 5.0](https://dotnet.microsoft.com/download).

2. Run

```
./tools/install-dafny.sh
```

This will install VeriBetrFS's [custom version of Dafny](https://github.com/secure-foundations/dafny) which includes our linear types extension.

3. Install Python dependencies for our build chain.

```
pip3 install toposort
```

4. Install clang and libc++. You probably already have this if you're on a Mac.

# Building and running

## VeriBetrFS dafny

The above steps should have created a local installation of Dafny into `.dafny/`.
You can run veribetrfs-dafny manually with `tools/local-dafny.sh`.
The Makefile will use veribetrfs-dafny by default.

## Verify the software stack

Adjust -j# to exploit all of your cores.
```
make -j4 status
```

Expect this to take at least a couple of hours of CPU time. When it completes, it will
produce the result file `build/Impl/Bundle.i.status.pdf`. You should expect the results,
ideally, to be all green (passes verification). In practice, there will often be some
non-green files where work is in progress, unless we've recently made a push to get
everything green for a release build.

## Lightweight benchmarking

We have a very brief benchmark for a quick sanity check that everything is working. Note that you don't need to run verification before building and running the system.

```
make elf # Compile VeriBetrFS via the C++ backend
./build/Veribetrfs --benchmark=random-queries
```

## YCSB

YCSB is a serious benchmark suite for production key-value stores.

The C++ YCSB benchmark library and rocksdb are vendored as a git submodule. Run

```
$ ./tools/update-submodules.sh
```

to initialise git submodules and to update the checkouts of the modules.
We also recommend setting:

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

# Contributing

See CONTRIBUTING.md for our contributing guidelines.
