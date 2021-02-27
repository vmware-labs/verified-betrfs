#!/usr/bin/env python3

# Copyright 2018-2021 VMware, Inc.
# SPDX-License-Identifier: MIT

import matplotlib
import matplotlib.pyplot as plt
import numpy as np
import re
import sys

def parse(filename):
    t = 0
    os_map_total = {}
    os_map_heap = {}
    malloc_total = {}
    for line in open(filename, "r").readlines():
        fields = line.split()
        if line.startswith("os-map-total"):
            os_map_total[t] = int(fields[1])
            os_map_heap[t] = int(fields[3])
            malloc_total[t] = int(fields[5])
            t += 1
        if line.startswith("ma-coarse-histogram"):
            size = fields[1]
            allocations[size][t] = int(fields[5))
        if line.startswith("ma-total"):
            allocations[size]["total"] = int(fields[4))
        if line.startswith("veribetrkv [op] sync"):
            completed[t] = int(fields[4])

    xs = range(t)
    fig, axes = plt.subplots(4, 1)

    rate = [float(completed[t])/t for t in completed]
    line, = axes[1].plot(xs, rate);

#    ax2 = ax1.twinx()
#
#    map_ratios = [float(os_map_total[t])/malloc_total[t] for t in xs]
#    line, = ax2.plot(xs, map_ratios, color="orange", linestyle="--")
#    line.set_label("map-malloc ratio")
#    heap_ratios = [float(os_map_heap[t])/malloc_total[t] for t in xs]
#    line, = ax2.plot(xs, heap_ratios, "r", linestyle="--")
#    line.set_label("heap-malloc ratio")
#
#    ax2.set_ylim(bottom = 0, top=3)
#    ax2.set_ylabel("x/malloc ratio")
#    ax2.legend(loc = "lower right")
#
#    trunc = 500 if len(map_ratios)>500 else 0 # initial reports are thrown off by weight of the executable
#    max_ratio = max(map_ratios[trunc:])   
#    max_t = map_ratios.index(max_ratio)
#    max_msg = "map-malloc ratio\nmax: %.2f @ %ds" % (max_ratio, max_t)
#    print(max_msg)
#    plt.text(max_t, max_ratio, max_msg)
#
#    scaleGB = 1e-9;
#    line, = ax1.plot(xs, [os_map_total[t]*scaleGB for t in xs], color="orange")
#    line.set_label("os-map-total")
#    line, = ax1.plot(xs, [os_map_heap[t]*scaleGB for t in xs], "r")
#    line.set_label("os-map-heap")
#    line, = ax1.plot(xs, [malloc_total[t]*scaleGB for t in xs], "b")
#    line.set_label("malloc")
#    ax1.set_ylabel("GB")
#    ax1.legend()
    
    figname = "%s-timeseries.png" % filename
    plt.savefig(figname)
    #plt.show()
    
parse(sys.argv[1])
