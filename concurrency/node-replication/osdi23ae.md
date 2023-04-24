# Setup

1. Allocate a CloudLab machine: results up to 64 cores can be reproduced on c6420 machines. [Click here to instantiate a specialized profile that allocates one c6420 machine on CloudLab with Ubuntu 20.04.](https://www.cloudlab.us/p/sandstorm/nr-osdi23-ae). If these machines aren't available, make a reservation. Other machine types might work as well, but, due to low core counts, won't replicate much of the graph from the paper, since that was run on a high-core-count, quad-socket machine. For example, using the `small-lan` profile with node type e.g. `c6220` and Ubuntu 20.04 has also been tested, and it reproduces the graph up to about 32 cores.
2. ssh to the machine.
3. `bash`
4. Checkout the artifact repository and `cd` into its root directory.
5. `./concurrency/node-replication/cloudlab-setup`

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

The results should show the same trends as Figure 16, though, since the CloudLab machine have lower core counts the peak numbers and full graph won't be visible.
