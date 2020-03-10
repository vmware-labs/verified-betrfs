#!/usr/bin/env python3
import matplotlib
import matplotlib.pyplot as plt
import numpy as np
import re

def parse():
    t = 0
    proc_heap = {}
    malloc_total = {}
    for line in open("malloc-exp/x-20m-uv4gb-200count", "r").readlines():
        if line.startswith("proc-heap"):
            fields = line.split()
            proc_heap[t] = int(fields[1])
            malloc_total[t] = int(fields[3])
            t += 1

    xs = range(t)
    fig, ax1 = plt.subplots()
    ax2 = ax1.twinx()

    ratios = [float(proc_heap[t])/malloc_total[t] for t in xs]
    line, = ax2.plot(xs, ratios, "g")
    line.set_label("ratio")
    ax2.set_ylim(bottom = 0)
    ax2.set_ylabel("heap/malloc ratio")
    ax2.legend(loc = "upper right")
    max_ratio = max(ratios)
    max_t = ratios.index(max_ratio)
    max_msg = "max: %.2f @ %ds" % (max_ratio, max_t)
    print(max_msg)
    plt.text(max_t, max_ratio, max_msg)

    line, = ax1.plot(xs, [proc_heap[t] for t in xs])
    line.set_label("OS heap")
    line, = ax1.plot(xs, [malloc_total[t] for t in xs])
    line.set_label("malloc")
    ax1.set_ylabel("GB")
    ax1.legend()
    
    plt.savefig("malloc-exp/heap-to-malloc.png")
    #plt.show()
    
parse()
