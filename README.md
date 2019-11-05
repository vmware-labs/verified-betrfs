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

## (In)active branches

Active:

```
2019-11-04 13:46:46 -0500 18 hours ago 	origin/master
2019-10-15 16:36:20 +0200 3 weeks ago 	origin/free-ref
```

Inactive:

```
2019-11-04 19:40:33 -0500 12 hours ago 	origin/indirection-table-size-bound
2019-11-04 12:51:18 -0500 19 hours ago 	origin/remove-min
2019-11-01 21:49:46 -0400 3 days ago 	origin/ref-counting
2019-10-23 22:57:06 -0400 12 days ago 	origin/compile
2019-10-23 18:24:51 -0400 13 days ago 	origin/indirection-table-refactor
2019-10-22 15:46:05 -0400 2 weeks ago 	origin/integrate-bitmap
2019-10-11 14:03:31 -0400 4 weeks ago 	origin/reference-counts
2019-10-11 14:03:31 -0400 4 weeks ago 	origin/mutablemap-iter
2019-10-02 14:05:09 -0400 5 weeks ago 	origin/benchmarking
2019-09-19 00:01:58 -0400 7 weeks ago 	origin/passive-aggressive-unverified
2019-09-17 21:49:21 -0400 7 weeks ago 	origin/mutable-bucket
2019-09-07 10:09:43 -0700 8 weeks ago 	origin/mutable-btree
2019-09-06 11:39:16 -0700 9 weeks ago 	origin/talk
2019-09-03 22:10:34 -0400 9 weeks ago 	origin/eviction
2019-08-30 13:55:43 -0400 10 weeks ago 	origin/weights
2019-08-23 00:36:06 -0700 2 months ago 	origin/awesome-refactor
2019-08-20 18:05:19 -0700 3 months ago 	origin/noalias
2019-08-20 13:04:04 -0700 3 months ago 	origin/noalias-notes
2019-08-13 17:20:06 -0700 3 months ago 	origin/capped-experiment
2019-08-09 23:05:42 -0700 3 months ago 	origin/do-split-2
2019-08-02 14:07:47 -0700 3 months ago 	origin/wire-hash-map
2019-07-25 16:49:56 -0700 3 months ago 	origin/mutable-map
2019-07-10 16:32:29 -0700 4 months ago 	origin/log
2019-07-02 17:44:52 -0700 4 months ago 	origin/kill-split-and-merge
2019-06-28 07:49:00 -0700 4 months ago 	origin/makefile-recovery
2019-06-25 22:54:58 -0700 4 months ago 	origin/more-flush-merges-2
2019-06-18 11:05:11 -0700 5 months ago 	origin/proof-simplification
2019-06-12 17:00:18 -0700 5 months ago 	origin/garbage-collection
2019-06-07 18:13:14 -0700 5 months ago 	origin/non-abstract-modules
```
