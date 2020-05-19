#!/usr/bin/env python3

import matplotlib.pyplot as plt

def parse(datafile):
    lines = open(datafile).readlines()
    zipped = [[float(v) for v in  l.split()] for l in lines]
    return list(zip(*zipped))

def plot(reprdata):
    fig = plt.figure()
    ax = fig.add_subplot(111)
    sizes = reprdata[0]
    xpos = range(len(sizes))
    times = reprdata[1]
    rates = [sizes[i]/times[i]/1000 for i in xpos]
    line = ax.bar(xpos, rates, color="green")
    line.set_label("dynamic frames")
    ax.set_xticks(xpos)
    prettySizes = ["%d" % (size/(1<<20)) for size in sizes]
    ax.set_xticklabels(prettySizes)
    ax.set_xlabel(r"inserts (${\times} 2^{20}$)", usetex=True)
    ax.set_ylabel(r"inserts/sec ($\times 1000$)", usetex=True)
    ax.legend()
    fig.savefig("data/btree-perf.pdf")

reprdata = parse("data/btree-repr.data")
plot(reprdata)
