#!/usr/bin/env python3

import glob
import numpy as np
import matplotlib.pyplot as plt

class Case:
    def __init__(self):
        self.metadata = {}
        self.data = {}  # maps insert size to list of results at that size

    def branch(self):
        return self.metadata["branch"]

    def add(self, k, v):
        if k not in self.data: self.data[k] = []
        self.data[k].append(v)

    def update(self, other):
        for k in set(self.sizes()).union(other.sizes()):
            self.data[k] = self.data.get(k, []) + other.data.get(k, [])

    def sizes(self):
        return list(self.data.keys())

    def rates(self, size):
        return [size/t for t in self.data[size]]

    def rate_mean(self, size):
        return np.mean(self.rates(size))

    def rate_stddev(self, size):
        return np.std(self.rates(size))

def parse(datafile):
    case = Case()
    for line in open(datafile).readlines():
        fields = line.split()
        if line.startswith("METADATA"):
            case.metadata[fields[1]] = " ".join(fields[2:])
        else:
            size = int(fields[0])
            total_time = float(fields[1])
            case.add(size, total_time)
    return case

def parseSeveral(datafiles):
    cases_by_branch = {}
    for datafile in datafiles:
        case = parse(datafile)
        if case.branch() in cases_by_branch:
            case.update(cases_by_branch[case.branch()])
        cases_by_branch[case.branch()] = case
    return cases_by_branch

def plot(data):
    fig = plt.figure()
    ax = fig.add_subplot(111)

    width=0.4
    num_cases = len(data.values())
    for casei, case in enumerate(data.values()):
        sizes = case.sizes()

        xpos = range(len(sizes))
        rates = [case.rate_mean(sizes[i])/1000 for i in xpos]
        errs = [case.rate_stddev(sizes[i])/1000 for i in xpos]

        line = ax.bar([x+width*casei for x in xpos], rates, yerr=errs, width=width)
        line.set_label(case.branch())
    ax.set_xticks([x + width*(num_cases-1)/2 for x in xpos])
    prettySizes = ["%d" % (size/(1<<20)) for size in sizes]
    ax.set_xticklabels(prettySizes)
    ax.set_xlabel(r"inserts (${\times} 2^{20}$)", usetex=True)
    ax.set_ylabel(r"inserts/sec ($\times 1000$)", usetex=True)

    ax.legend()
    fig.savefig("data/btree-perf.pdf")

data = parseSeveral(glob.glob("expresults/btree-tp-insert/*.data"))
plot(data)
