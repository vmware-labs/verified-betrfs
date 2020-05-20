#!/usr/bin/env python3

import re
import math
import numpy as np
import matplotlib.pyplot as plt
import glob

EXPERIMENT="veri_time_09"

class SymbolPile:
    def __init__(self):
        self.symbols = {}

    def put_replica(self, name, time):
        if name not in self.symbols:
            self.symbols[name] = []
        self.symbols[name].append(time)

def parse_one(datafile, pile):
    symbol_parts = {}

    def record_part(symbol, part, time):
        if symbol not in symbol_parts:
            symbol_parts[symbol] = []
        symbol_parts[symbol].append(time)
        # ignore the part. Who cares if some symbols don't have an Impl$$ part?

    for line in open(datafile).readlines():
        #print (line)
        mo = re.compile("Verifying (\S*) \.\.\.").search(line)
        if mo!=None:
            part,symbol = mo.groups()[0].split("$$")
        mo = re.compile("\[([0-9\.]+) s,.*\]  verified").search(line)
        if mo!=None:
            time = float(mo.groups()[0])
            record_part(symbol, part, time)

    # now sum up the parts and put them in the statistics pile
    for symbol,part_times in symbol_parts.items():
        pile.put_replica(symbol, sum(part_times))

def parse_all():
    pile = SymbolPile()
    resultsfiles = glob.glob("expresults/%s-*" % EXPERIMENT)
    for file in resultsfiles:
        parse_one(file, pile)

    mean_times = []
    for symbol,replica_times in pile.symbols.items():
        mean_times.append(np.mean(replica_times))

    mean_times.sort()
    N = len(mean_times)
    def cdist(i):
        return i*1.0/N
    ys = [cdist(i) for i in range(N)]
    def complog(y):
        return -math.log10(1-y)
    ys = [complog(y) for y in ys]

    fig = plt.figure()
    ax = fig.add_subplot(111)
    ax.plot(mean_times, ys)

    thresh = 20
    idx,t = next((idx,t) for idx,t in enumerate(mean_times) if t>thresh)
    idx = idx - 1
    t = mean_times[idx]
    ypos = complog(cdist(idx))
    y0 = complog(0)
    ax.plot([0, t, t], [ypos, ypos, y0])
    ax.text(0, ypos*1.01, "%.1f%% faster than %ds" % (cdist(idx)*100, thresh))
    print(idx, t, len(mean_times))

    yticks = range(4)
    ax.set_yticks(yticks)
    ax.set_yticklabels([1-math.pow(10, -y) for y in yticks])
    ax.set_xlabel("time to verify definition, method or lemma (s)")
    ax.set_ylabel("cumulative fraction (log scale)")

    fig.savefig("data/verification-times.pdf")

def main():
    parse_all()

main()
