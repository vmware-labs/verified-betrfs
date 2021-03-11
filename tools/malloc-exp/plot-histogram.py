#!/usr/bin/env python3

# Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
# SPDX-License-Identifier: BSD-2-Clause

import matplotlib
import matplotlib.pyplot as plt
import numpy as np
import re
#import json

def parse_one_histogram(line):
    #return json.loads(line)
    assert line[0] == "{"
    assert line[-2:] == "}\n"
    line = line[1:-2]
    pairs = line.split(",")[:-1]
    histo = {}
    for pair in pairs:
        size,count = map(int, pair.split(":"))
        if count>0:
            histo[size] = count
    return histo

def cdf(histo, by_size):
    sizes = list(histo.keys())
    sizes.sort()
    xs = []
    ys = []
    accum = 0
    for size in sizes:
        count = histo[size]
        accum += count * size if by_size else count
        xs.append(size)
        ys.append(accum)
    #print(xs)
    # normalize ys to 0..1
    ys = [y/float(accum) for y in ys]
    #print(ys)
    return xs, ys

def parse():
    t = 0
    proc_heap = {}
    malloc_total = {}
    histos = {}
    for line in open("malloc-exp/histograms", "r").readlines():
        if line.startswith("proc-heap"):
            fields = line.split()
            proc_heap[t] = int(fields[1])
            malloc_total[t] = int(fields[3])
            t += 1
        
        if line.startswith("{"):
            histos[t] = parse_one_histogram(line)

    max_histo_t = max(histos.keys())
    print(max_histo_t)
    max_histo = histos[max_histo_t]
    print(max_histo)

    # accumulate the CDF
    line, = plt.plot(*cdf(max_histo, True))
    line.set_label("by size")
    line, = plt.plot(*cdf(max_histo, False))
    line.set_label("by allocation count")
    plt.xscale("log")
    plt.legend()
    
    plt.savefig("malloc-exp/size-cdf.png")
    #plt.show()
    
parse()
