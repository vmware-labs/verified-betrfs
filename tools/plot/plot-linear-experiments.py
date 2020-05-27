#!/usr/bin/env python3

import glob
import numpy as np
import matplotlib.pyplot as plt

class Case:
    def __init__(self):
        self.data = {}  # maps insert size to list of results at that size

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

class Exp:
    def __init__(self):
        self.metadata = {}
        self.cases = {"read": Case(), "write": Case()}

    def branch(self):
        return self.metadata["branch"]

    def update(self, other):
        for mode in self.cases.keys():
            self.cases[mode].update(other.cases[mode])

def parse(datafile):
    exp = Exp()
    for line in open(datafile).readlines():
        fields = line.split()
        if line.startswith("METADATA"):
            exp.metadata[fields[1]] = " ".join(fields[2:])
        else:
            size = int(fields[0])
            mode = fields[1]
            time_ms = float(fields[3])
            case = exp.cases[mode]
            case.add(size, time_ms)
    return exp

def parseSeveral(datafiles):
    exps_by_branch = {}
    for datafile in datafiles:
        exp = parse(datafile)
        if exp.branch() in exps_by_branch:
            exp.update(exps_by_branch[exp.branch()])
        exps_by_branch[exp.branch()] = exp
    return exps_by_branch

def plot(data):
    fig = plt.figure()
    width=0.4

    def plot_case(ax, mode, label, want_xlabel):
        num_cases = len(data.values())
        for expi, exp in enumerate(data.values()):
            case = exp.cases[mode]
            sizes = case.sizes()

            xpos = range(len(sizes))
            rates = [case.rate_mean(sizes[i])/1000 for i in xpos]
            errs = [case.rate_stddev(sizes[i])/1000 for i in xpos]

            line = ax.bar([x+width*expi for x in xpos], rates, yerr=errs, width=width)
            line.set_label(exp.branch())
        ax.set_xticks([x + width*(num_cases-1)/2 for x in xpos])
        prettySizes = ["%d" % (size/(1000000)) for size in sizes]
        ax.set_xticklabels(prettySizes)
        if want_xlabel:
            ax.set_xlabel(r"Mi operation count (${\times} 2^{20}$)", usetex=True)
        ax.set_ylabel(r"M %s/sec ($\times 10^6$)" % label, usetex=True)
        ax.legend()

    plot_case(fig.add_subplot(2, 1, 1), "read", "reads", want_xlabel=False)
    plot_case(fig.add_subplot(2, 1, 2), "write", "inserts", want_xlabel=True)

    fig.savefig("data/btree-perf.pdf")

data = parseSeveral(glob.glob("expresults/btree-tp/*.data"))
plot(data)
