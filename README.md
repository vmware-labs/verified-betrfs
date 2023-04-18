This artifact contains two major components:

 * Run LinearDafny to verify our Dafny source and translate it into C++ source. This corresponds primarily to Sec. 7.1 of our paper.
 * Run the benchmarks. This corresponds to Sec. 7.2.


Our artifact includes the expected C++ output from step 1, which is needed by step 2.
Therefore, each component may be evaluated independently without dependency on the other.

# Running LinearDafny

There are two options, using Docker or using a manual install.

## Docker

Just run:

```
./run-dafny-in-docker.sh
```

This will build the docker container and run all the important LinearDafny commands.
Expect Dafny verification to take around 10-20 minutes.

The Dockerfile is configured with `--platform=linux/amd64`, so e.g., so on an `arm` machine,
it might run slow because it has to emulate.

## Manual

First, you need to install .NET Core 5.0 from https://dotnet.microsoft.com/download.
Unfortunately, this is technically out-of-support now, so it may be difficult to get
it to work on newer operating systems.

Additionally:

 * Install `sloccount` (try `apt-get install sloccount` or `brew install sloccount`)
 * Install `pip3` and run `pip3 install toposort`

To finish set-up, run,

```
./tools/artifact-setup-dafny.sh
```

Finally, run LinearDafny (you can do these steps in either order):

```
./build-cpp-source.sh
./run-verifier.sh
```

Expect `run-verifier.sh` to take about 10-20 minutes. 

## Evaluating the output

Regardless of which steps you followed above, the results should be in the `build` directory.

### Verification results

The following PDF files should summarize the verification results:

```
./build/concurrency/bank-paper/Impl.i.status.pdf
./build/concurrency/hashtable/Interface.i.status.pdf
./build/concurrency/node-replication/Interface.i.status.pdf
./build/concurrency/scache/Bundle.i.status.pdf
```

These correspond to the 4 case studies in Figure 15 of our paper.
You should expect to see all green to indicate successful verification. 
Dafny can glitch out sometime but in that case,
you would probably expect to see just 1-2 files marked as failing.
The Docker container seems to be more reliable, though.

### Source code summarization and verification times

Next, check the file:

```
./build/concurrency/SeagullBundle.i.lcreport
```

The file contains the data from the paper's Figure 15 as well as other stats mentions in
Section 7.1.

### Translated C++ source

Finally, you can compare the generated C++ files with the ones includes in this artifact.

TODO list the files, and if there any expected differences, make sure to mention them
and explain them

# Running benchmarks
