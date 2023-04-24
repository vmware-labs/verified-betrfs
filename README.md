This artifact contains two major components:

 * Run LinearDafny to verify our Dafny source and translate it into C++ source. This corresponds primarily to Sec. 7.1 of our paper.
 * Run the benchmarks. This corresponds to Sec. 7.2.

See the following files for directions:

 * `ae-instructions-dafny-verification.md` for the verification step
 * `concurrency/node-replication/osdi23ae.md` for benchmarks of NR
 * `concurrency/SplinterDB/README.md` for benchmarks of SplinterCache

These 3 parts are designed to be independent.

Note that the primary claim of Sec 7.2 is that each IronSync implementation matches the performance of its corresponding reference implementation within a small tolerance.  We expect that this feature will reproduce on most hardware that can run the software. Reproducing the exact performance characteristics requires more specific hardware. The benchmark instruction pages provide more specific hardware recommendations.

# Getting started

We recommend x86 Ubuntu for each of the steps. The first step comes with a Docker container, so can probably be done on any platform. However, the benchmarks _must_ be run on x86 Ubuntu.

 * See `ae-instructions-dafny-verification.md` and follow the instructions for setting up Dafny.
 * For each benchmarked system, follow the instructions for building the benchmarks and check that you can start them. See both:
    * `concurrency/node-replication/osdi23ae.md`
    * `concurrency/SplinterDB/README.md`

# Detailed Instructions

 * See `ae-instructions-dafny-verification.md` and follow the directions in the "Evaluating results" section. Expect this step to take 10-30 minutes.
 * See each of the benchmark pages and follow the instructions for running the benchmarks, using appropriate hardware. Check that the results show that the IronSync versions have comparable performance to the reference implementations.
