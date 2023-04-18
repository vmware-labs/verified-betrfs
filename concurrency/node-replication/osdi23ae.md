# Setup

1. Allocate a CloudLab machine: results up to 64 cores can be reproduced on c6420 machines. [Click here to instantiate a specialized profile that allocates one c6420 machine on CloudLab with Ubuntu 20.04.](https://www.cloudlab.us/p/sandstorm/nr-osdi23-ae).
2. ssh to the machine.
3. `bash`
4. `git clone git@github.com:rstutsman/verified-betrfs.git`
5. `cd verified-betrfs`
6. `git checkout concurrency-experiments`
7. `./concurrency/node-replication/cloudlab-setup`

# Setup Paths/Environment
1. `export PATH="$HOME/.dotnet:$PATH"`
2. `source "$HOME/.cargo/env"`

# Compile the NR Benchmarks

1. `cd concurrency/node-replication`
2. `./compile-bench.sh`


# Run the Benchmarks

1. `./bench.py`


# View the Results

1. `scp $CLOUDLABHOST:skylake4x-throughput-vs-cores-compare-locks.pdf .`
2. Open `skylake4x-throughput-vs-cores-compare-locks.pdf` which corresponds to Figure 16 in the paper. The figure is replotted incrementally after each new data point is taken as the experiments runs.
