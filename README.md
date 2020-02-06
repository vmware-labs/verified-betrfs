# Setting things up

Make sure you have `make`, `mono`, and `wget`

```
mono -V
which wget
```

## Set up dafny (and boogie, z3)

*From the project root*, run:

```
./tools/install-dafny.sh
```

This will download and compile boogie, veri-dafny, z3.

You can run veri-dafny with `./.dafny/bin/dafny`, the Makefile will use veri-dafny by default

## YCSB

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

