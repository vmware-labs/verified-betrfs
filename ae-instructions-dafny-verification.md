# Running Linear Dafny

You can either run on a Docker or install Linear Dafny locally.
We recommend the Docker as it is the most reliable.
For local install, you need to be on x86 Ubuntu.

## Option 1. Docker (recommended)

Install Docker, and then just run:

```
./run-dafny-in-docker.sh
```

This will build the docker container and run all the important LinearDafny commands.
Expect Dafny verification to take around 10-20 minutes.

The Dockerfile is configured with `--platform=linux/amd64`, so e.g., so on an `arm` machine,
it might run slow because it has to emulate. On MacOS (arm) you can enable rosetta for docker to make it faster.

## Option 2. Script install

Set-up Linear Dafny:

```
source ./dotnet-and-dafny-setup.sh
```

Run Linear Dafny (make sure to run the previous command via `source`):

```
./run-verifier.sh
```

## Option 3. Manual

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

Finally, run LinearDafny:

```
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
