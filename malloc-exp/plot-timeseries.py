#!/usr/bin/env python3
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

def parse(filename):
    t = 0
    os_map_total = {}
    os_map_heap = {}
    malloc_total = {}
    allocations = {"small": {} , "large": {}, "total": {}}
    first_op_completed_t = None
    ops_completed = {}
    scopes = {}
    for line in open(filename, "r").readlines():
        fields = line.split()
        if line.startswith("os-map-total"):
            os_map_total[t] = int(fields[1])
            os_map_heap[t] = int(fields[3])
            malloc_total[t] = int(fields[5])
            t += 1
        if line.startswith("ma-coarse-histogram") and len(fields)>5:
            size = fields[1]
            allocations[size][t] = int(fields[5])
        if line.startswith("ma-total"):
            allocations["total"][t] = int(fields[4])
        if line.startswith("veribetrkv [op] sync"):
            if first_op_completed_t == None:
                first_op_completed_t = t - 2
            ops_completed[t] = int(fields[4])
        if line.startswith("ma-scope") and len(line)>53:
            base = 9
            width = 12+1
            #width = 14+1
            labeloff = base+width*4
            label = line[base+width*4:].strip()
            #print("line:", line)
            #print("line[%d]: %s" %( labeloff, line[labeloff]))
            #print("label:", label)
            if label!="label" and not label.startswith("----"):
                total_count = line[base:base+width]
                open_count = line[base+width:base+width*2]
                total_byte = line[base+width*2:base+width*3]
                open_byte = line[base+width*3:base+width*4]
                arow = ARow(total_count, open_count, total_byte, open_byte)
                if label not in scopes:
                    scopes[label] = {}
                scopes[label][t] = arow

    fig, axes = plt.subplots(5, 1, figsize=(5,10))
    plt.subplots_adjust(left=0.15, right=0.95, hspace=0.4, top=0.95, bottom=0.05);

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
    xs = allocations["total"].keys()
    line, = axes[1].plot(xs, [allocations["total"][t]/GB for t in xs])
    line.set_label("malloc total")
    line, = axes[1].plot(xs, [allocations["small"][t]/GB for t in xs])
    line.set_label("malloc small")
    line, = axes[1].plot(xs, [(allocations["small"][t] + allocations["large"][t])/GB for t in xs])
    line.set_label("malloc large")
    xs = [t for t in xs if t in os_map_total]
    line, = axes[1].plot(xs, [os_map_total[t]/GB for t in xs])
    line.set_label("OS mapping")
    axes[1].set_xlim(left = 0, right=t_end)
    axes[1].legend()
    axes[1].set_title("allocations")
    axes[1].set_ylabel("GB")

    label_bytearys = "seq-from-array.[T = unsigned char]"
    focus_bytearys = scopes[label_bytearys]
    xs_bytearys = [t for t in focus_bytearys]
    ys = [focus_bytearys[t].open_byte/GB for t in xs_bytearys]
    line, = axes[2].plot(xs, ys)
    line.set_label("[byte] bytes");
    axes[2].set_title(label_bytearys)
    axes[2].set_ylabel("GB")
    axes[2].legend()

    a2twin = axes[2].twinx()
    ys_bytearys = [focus_bytearys[t].open_count for t in xs_bytearys]
    line, = a2twin.plot(xs, ys_bytearys)
    line.set_label("[byte] count");
    a2twin.set_ylabel("count")

    label_nodes = ".NodeImpl_Compile::Node"
    focus_nodes = scopes[label_nodes]
    xs_nodes = [t for t in focus_nodes]
    ys_nodes = [focus_nodes[t].open_count for t in xs_nodes]
    line, = a2twin.plot(xs, ys_nodes)
    line.set_label("Node count")
    a2twin.legend(loc="right")

    xs_ratio = [t for t in xs_bytearys if t in xs_nodes]
    ys_ratio = [focus_bytearys[t].open_byte/float(focus_nodes[t].open_count)/MB for t in xs_ratio]
    axes[3].plot(xs_ratio, ys_ratio)
    axes[3].set_title("bytes in byte[] per Node")
    axes[3].set_ylabel("MB")
    axes[3].set_ylim(bottom = 7)

    xs_byteToMalloc = [t for t in xs_bytearys]
    ys_byteToMalloc = [ allocations["total"][t] / focus_bytearys[t].open_byte for t in xs_byteToMalloc]
    line, = axes[4].plot(xs_byteToMalloc, ys_byteToMalloc)
    line.set_label("malloc total / bytes in byte[]")
    axes[4].set_ylim(bottom = 0)
    xs_mallocToOs = allocations["total"].keys()
    ys_mallocToOs = [os_map_total[t] / allocations["total"][t] for t in xs_mallocToOs]
    line, = axes[4].plot(xs_mallocToOs, ys_mallocToOs)
    line.set_label("OS mapping / malloc total")
    axes[4].legend()

    figname = "%s-timeseries.png" % filename
    plt.savefig(figname)
    #plt.show()
    
parse(sys.argv[1])
