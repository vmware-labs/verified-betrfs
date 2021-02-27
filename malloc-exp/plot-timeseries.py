#!/usr/bin/env python3

# Copyright 2018-2021 VMware, Inc.
# SPDX-License-Identifier: MIT

import matplotlib
import matplotlib.pyplot as plt
import numpy as np
import re
import sys

class ARow:
    def __init__(self, total_count, open_count, total_byte, open_byte):
        self.total_count = int(total_count)
        self.open_count = int(open_count)
        self.total_byte = int(total_byte)
        self.open_byte = int(open_byte)

field_width = 14+1
arow_width = field_width*4 - 1

def parse_arow(s):
    assert(len(s) == arow_width)
    total_count = s[:field_width]
    open_count = s[field_width:field_width*2]
    total_byte = s[field_width*2:field_width*3]
    open_byte = s[field_width*3:field_width*4]
    return ARow(total_count, open_count, total_byte, open_byte)

def match_arow_line(token, line):
    if not line.startswith(token + " "):
        return None
    arow = parse_arow(line[len(token)+1:len(token)+1+arow_width])
    label = line[len(token)+1+arow_width+1:]
    return (arow, label)

def parse(filename):
    t = 0
    os_map_total = {}
    os_map_heap = {}
#    allocations = {"small": {} , "large": {}, "total": {}}
    microscopes = {}
    first_op_completed_t = None
    ops_completed = {}
    scopes = {}
    kvl_underlying = {}
    kvl_underlying_count = {}
    for line in open(filename, "r").readlines():
        line = line.strip()
        fields = line.split()
        if line.startswith("os-map-total"):
            os_map_total[t] = int(fields[1])
            os_map_heap[t] = int(fields[3])
            t += 1
        if line.startswith("veribetrkv [op] sync"):
            if first_op_completed_t == None:
                first_op_completed_t = t - 2
            ops_completed[t] = int(fields[4])

        mo = match_arow_line("ma-scope", line)
        if mo:
            arow,label = mo
            if label not in scopes:
                scopes[label] = {}
            scopes[label][t] = arow

        mo = match_arow_line("ma-microscope", line)
        if mo:
            arow,label = mo
            label = label.split()[-1]   # suffix word. Sorry.
            if label not in microscopes:
                microscopes[label] = {}
            microscopes[label][t] = arow
        
        if line.startswith("allocationreport stop underyling_count"):
            kvl_underlying_count[t] = int(fields[3])
            kvl_underlying[t] = int(fields[5])

    fig, axes = plt.subplots(6, 1, figsize=(5,12))
    plt.subplots_adjust(left=0.10, right=0.90, hspace=0.4, top=0.95, bottom=0.05);

    t_end = max(os_map_total.keys())

    Kilo = 1000
    def smoothedThroughput(window):
        xs = [t for t in ops_completed if t>0 if t>=window]
        ys = [(ops_completed[t] - ops_completed[t-window])/float(window)/Kilo for t in xs]
        axes[0].plot(xs, ys)
    smoothedThroughput(10)
    smoothedThroughput(100)
    axes[0].set_xlim(left = 0, right=t_end)
    axes[0].set_ylim(bottom = 0)
    axes[0].set_title("op throughput")
    axes[0].set_ylabel("Kops/sec")

    xs = [t for t in ops_completed]
    def aggregateAt(time, label):
        if time > xs[-1]:
            return
        aggregate = (ops_completed[time] - ops_completed[xs[0]])/float(time-xs[0])/Kilo
        axes[0].text(time, aggregate, "mean %.1f" % aggregate, horizontalalignment="right")
    aggregateAt(xs[-1], "end")
    aggregateAt(1000, "1000s")

    MB = float(1<<20)
    GB = float(1<<30)
    xs = microscopes["total"].keys()
    line, = axes[1].plot(xs, [microscopes["total"][t].open_byte/GB for t in xs])
    line.set_label("malloc total")
    line, = axes[1].plot(xs, [microscopes["coarse-small"][t].open_byte/GB for t in xs])
    line.set_label("malloc small")
    line, = axes[1].plot(xs, [(microscopes["coarse-small"][t].open_byte + microscopes["coarse-large"][t].open_byte)/GB for t in xs])
    line.set_label("malloc large")
    xs = [t for t in xs if t in os_map_total]
    line, = axes[1].plot(xs, [os_map_total[t]/GB for t in xs])
    line.set_label("OS mapping")
    axes[1].set_xlim(left = 0, right=t_end)
    axes[1].legend()
    axes[1].set_title("allocations")
    axes[1].set_ylabel("GB")

    #label_bytearys = "seq-from-array.[T = unsigned char]"
    label_bytearys = "in_amass.[T = unsigned char]"
    focus_bytearys = scopes[label_bytearys]
    xs_bytearys = [t for t in focus_bytearys]
    ys_bytearys = [focus_bytearys[t].open_byte/GB for t in xs_bytearys]
    line, = axes[2].plot(xs_bytearys, ys_bytearys)
    line.set_label("[byte] bytes");
    axes[2].set_title(label_bytearys)
    axes[2].set_ylabel("GB")
    axes[2].legend()

    a2twin = axes[2].twinx()
    ys_bytearys = [focus_bytearys[t].open_count for t in xs_bytearys]
    line, = a2twin.plot(xs_bytearys, ys_bytearys)
    line.set_label("[byte] count");
    a2twin.set_ylabel("count")

    label_nodes = ".NodeImpl_Compile::Node"
    focus_nodes = scopes[label_nodes]
    xs_nodes = [t for t in focus_nodes]
    ys_nodes = [focus_nodes[t].open_count for t in xs_nodes]
    line, = a2twin.plot(xs_nodes, ys_nodes)
    line.set_label("Node count")
    line, = a2twin.plot(xs_nodes, [microscopes["sfaLarge"][t].open_count for t in xs])
    line.set_label("amass count")
    line, = a2twin.plot(xs_nodes, [microscopes["esLarge"][t].open_count for t in xs])
    line.set_label("pagein count")
    a2twin.legend(loc="lower left")

#    xs_ratio = [t for t in xs_bytearys if t in xs_nodes]
#    ys_ratio = [focus_bytearys[t].open_byte/float(focus_nodes[t].open_count)/MB for t in xs_ratio]
#    print("fooi", len(ys_ratio))
#    axes[3].plot(xs_ratio, ys_ratio)
#    axes[3].set_title("bytes in byte[] per Node")
#    axes[3].set_ylabel("MB")
#    axes[3].set_ylim(bottom = 0)
    # stack chart of...
    stack = [
              (microscopes["esLarge"], "pagein"),
              (microscopes["sfaLarge"], "amass"),
              (scopes["in_amass.[T = unsigned char]"], "in_amass"),
            ]
    xs = [t for t in stack[0][0]]
    prev = [0 for t in xs]
    for i in range(len(stack)):
        (item,label) = stack[i]
        ys = [(item[xs[i]].open_byte + prev[i])/GB for i in range(len(xs))]
        line, = axes[3].plot(xs, ys)
        line.set_label(label)
        prev = ys
    line, = axes[3].plot(xs, [microscopes["total"][t].open_byte/GB for t in xs])
    line.set_label("malloc total")
    axes[3].legend()

    xs = [t for t in kvl_underlying]
    ys = [kvl_underlying[t]/GB for t in xs]
    line, = axes[4].plot(xs, ys)
    line.set_label("underlying sum");
    ys = [scopes["in_amass.[T = unsigned char]"][t].open_byte/GB for t in xs]
    line, = axes[4].plot(xs, ys)
    line.set_label("amass");
    axes[4].legend()
    axes[4].set_ylabel("GB")
    axes[4].set_title("malloc amass vs underlying sum")

    xs = [t for t in kvl_underlying_count]
    ys = [kvl_underlying_count[t] for t in xs]
    line, = axes[5].plot(xs, ys)
    line.set_label("reachable underlying allocs")
    ys = [scopes["in_amass.[T = unsigned char]"][t].open_count for t in xs]
    line, = axes[5].plot(xs, ys)
    line.set_label("amass live alloc count")
    axes[5].legend()
    axes[5].set_title("amass live allocs vs reachable underlying allocs")

    def cdf(axis, data):
        vals = list(data)
        vals.sort()
        sums = [0]
        for v in vals:
            sums.append(sums[-1] + v)
        sums = sums[1:]
        total = float(sums[-1])
        xs = vals
        ys = [sums[i]/total for i in range(len(vals))]
        axis.plot(xs, ys)
#    dataset = microscopes["sfaLarge"]
#    cdf(axes[4], [dataset[t].open_byte for t in dataset])

#    xs_byteToMalloc = [t for t in xs_bytearys]
#    ys_byteToMalloc = [ microscopes["total"][t].open_byte / focus_bytearys[t].open_byte for t in xs_byteToMalloc]
#    line, = axes[4].plot(xs_byteToMalloc, ys_byteToMalloc)
#    line.set_label("malloc total / bytes in byte[]")
#    axes[4].set_ylim(bottom = 0)
#    xs_mallocToOs = microscopes["total"].keys()
#    ys_mallocToOs = [os_map_total[t] / microscopes["total"][t].open_byte for t in xs_mallocToOs]
#    line, = axes[4].plot(xs_mallocToOs, ys_mallocToOs)
#    line.set_label("OS mapping / malloc total")
#    axes[4].legend()
#    axes[4].set_title("overheads")

    figname = "%s-timeseries.png" % filename
    plt.savefig(figname)
    #plt.show()
    
parse(sys.argv[1])
