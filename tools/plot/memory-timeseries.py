#!/usr/bin/env python3
import matplotlib
import matplotlib.pyplot as plt
import numpy as np
import sys
import operator
import bisect
from parser import Experiment
from PlotHelper import *
from TimeSeries import *

def plot_memory_timeseries(e):
    """e: Experiment"""

    plotHelper = PlotHelper(10)
    timeSeries = TimeSeries(e, plotHelper)

    def plotThroughput(ax):
        ax.set_title("op throughput")
        timeSeries.smoothedThroughput(ax, 10)
        cur = timeSeries.smoothedThroughput(ax, 100)
        ax.set_ylim(bottom = 0)
        ax.set_ylabel("Kops/sec")
        ax.set_xlabel("op num (K)")

        xs = [t for t in e.ops_completed]
        def aggregateAt(time, label):
            if time > xs[-1]:
                return
            aggregate = (e.ops_completed[time] - e.ops_completed[xs[0]])/float(time-xs[0])/Kilo
            msg = "mean %.1f" % aggregate
            if label == "end":
                msg += "\ncur %.2f" % cur
            ax.text(timeSeries.timeToKiloOp(time), aggregate, msg, horizontalalignment="right")
        aggregateAt(xs[-1], "end")
        t1m = timeSeries.opToTime(2000000)
        aggregateAt(t1m, "op1000k")
        
        axtwin = ax.twinx()
        ts = [t for t in e.ops_completed]
        ops = [e.ops_completed[t]/Kilo for t in xs]
        axtwin.plot(ops,ts, "g")
        axtwin.set_ylabel("time (s)")

    try: plotThroughput(timeSeries.nextOpAxis())
    except: raise

    def plotOSvsMalloc(ax):
        try:
            line, = ax.plot(*timeSeries.makePlot(e.microscopes["total"], lambda t: e.microscopes["total"][t].open_byte/GB))
            line.set_label("malloc total")
            line, = ax.plot(*timeSeries.makePlot(e.microscopes["coarse-small"], lambda t: e.microscopes["coarse-small"][t].open_byte/GB))
            line.set_label("malloc small")
            line, = ax.plot(*timeSeries.makePlot(e.microscopes["coarse-small"], lambda t:
                (e.microscopes["coarse-small"][t].open_byte + e.microscopes["coarse-large"][t].open_byte)/GB))
            line.set_label("malloc large")
        except:
            pass    # sorry, no e.microscopes
        line, = ax.plot(*timeSeries.makePlot(e.os_map_total, lambda t: e.os_map_total[t]/GB))
        line.set_label("OS mapping")
        line, = ax.plot(*timeSeries.makePlot(e.os_map_heap, lambda t: e.os_map_heap[t]/GB))
        line.set_label("OS heap mapping")

        maxX, maxY = max(e.os_map_total.items(), key=operator.itemgetter(1))
        ax.text(timeSeries.timeToKiloOp(maxX), maxY/GB, "max %.1fGB" % (maxY/GB), horizontalalignment="right")

        ax.legend()
        ax.set_title("allocations")
        ax.set_ylabel("GB")
    osVsMallocAxis = timeSeries.nextOpAxis()
    try: plotOSvsMalloc(osVsMallocAxis)
    except: pass

    def plotAmass(ax):
        focus_bytearys = e.scopes["in_amass.[T = unsigned char]"]
        line, = ax.plot(*timeSeries.makePlot(focus_bytearys, lambda t: focus_bytearys[t].open_byte/GB), linestyle="dotted")
        line.set_label("in_amass");
        ax.set_ylabel("GB")
        ax.legend()
    try: plotAmass(osVsMallocAxis)
    except: pass

    def plotNodes(ax):
        a2twin = ax.twinx()
        a2twin.set_ylabel("count")

        focus_bytearys = e.scopes["in_amass.[T = unsigned char]"]
        line, = a2twin.plot(*timeSeries.makePlot(focus_bytearys, lambda t: focus_bytearys[t].open_count))
        line.set_label("[byte] count");

        focus_nodes = e.scopes[".NodeImpl_Compile::Node"]
        line, = a2twin.plot(*timeSeries.makePlot(focus_nodes, lambda t: focus_nodes[t].open_count))
        line.set_label("Node count")
        line, = a2twin.plot(*timeSeries.makePlot(e.microscopes["sfaLarge"], lambda t: e.microscopes["sfaLarge"][t].open_count))
        line.set_label("amass count")
        line, = a2twin.plot(*timeSeries.makePlot(e.microscopes["esLarge"], lambda t: e.microscopes["esLarge"][t].open_count))
        line.set_label("pagein count")
        a2twin.legend(loc="lower left")

    amassAxis = timeSeries.nextOpAxis()
    try: plotAmass(amassAxis)
    except: pass
    try: plotNodes(amassAxis)
    except: pass

##    xs_ratio = [t for t in xs_bytearys if t in xs_nodes]
##    ys_ratio = [focus_bytearys[t].open_byte/float(focus_nodes[t].open_count)/MB for t in xs_ratio]
##    print("fooi", len(ys_ratio))
##    axes[3].plot(xs_ratio, ys_ratio)
##    axes[3].set_title("bytes in byte[] per Node")
##    axes[3].set_ylabel("MB")
##    axes[3].set_ylim(bottom = 0)

    def plotMemStackChart(ax):
        ax.set_title("memory consumption, stacked")
        # stack chart of...
        stack = [
                  (e.microscopes["esLarge"], "pagein"),
                  (e.microscopes["sfaLarge"], "amass"),
                  (e.scopes["in_amass.[T = unsigned char]"], "in_amass"),
                ]
        xs = [t for t in stack[0][0]]
        kops = timesToKiloOps(xs)
        prev = [0 for t in xs]
        for i in range(len(stack)):
            (item,label) = stack[i]
            ys = [(item[xs[i]].open_byte + prev[i]) for i in range(len(xs))]
            line, = ax.plot(kops, [v/GB for v in ys])
            line.set_label(label)
            prev = ys
            #prev = [0 for t in xs]
        line, = ax.plot(kops, [e.microscopes["total"][t].open_byte/GB for t in xs])
        line.set_label("malloc total")
        ax.legend()
        ax.set_ylabel("GB")
        ax.grid(axis="y", which="both", b=True)
    try: plotMemStackChart(timeSeries.nextOpAxis())
    except: pass

    def plotIORate(completed, label, color, ax):
        window = 20
        def windowedIO(completed, t):
            try:
                op_t = timeSeries.timeToOp(t)
                op_window = timeSeries.timeToOp(t - window)
                if op_t == None or op_window == None or op_window >= op_t:
                    return None
                #print(t, started[t], completed[t-window], op_t, op_window)
                return (completed[t] - completed[t-window])/(op_t - op_window)
            except ZeroDivisionError:
                return None
        line, = ax.plot(*timeSeries.makePlot(completed, lambda t: windowedIO(completed, t)), color=color)
        line.set_label(label)
        ax.set_title("IOs per operation, %ss window" % window)
        ax.legend()
        #ax.set_ylim(top=0.15)
        
    ioRateAxis = timeSeries.nextOpAxis()
    try:
        #axtwin = axes[4].twinx()
        plotIORate(e.writes_completed, "writes", "b", ioRateAxis)
        plotIORate(e.reads_completed, "reads", "r", ioRateAxis)
    except: raise

    def plotAccum(ax, accum_suite, divisor, ylabel):
        for categ in accum_suite:
            line, = ax.plot(*timeSeries.makePlot(e.accum[categ], lambda t: e.accum[categ][t]/divisor))
            line.set_label(categ)
        ax.set_title("internal accumulator")
        ax.set_ylabel(ylabel)
        ax.legend()

    try:
        plotAccum(timeSeries.nextOpAxis(), ("tree-nodes-count", "tree-buckets-count", "pkv-buckets-count", "weird-buckets-count"), 1, "count")
        plotAccum(timeSeries.nextOpAxis(), ("bucket-message-count", "bucket-key-count", "pivot-key-count"), 1e6, "M")
        bucketBytesAxis = timeSeries.nextOpAxis()
        plotAccum(bucketBytesAxis, ("bucket-message-bytes", "bucket-key-bytes", "pivot-key-bytes"), GB, "GB")
        last_t = max(e.accum["bucket-message-bytes"].keys())
        last_sum = sum([e.accum[c][last_t] for c in ["bucket-message-bytes", "bucket-key-bytes", "pivot-key-bytes"]])/GB
        msg = "total: %.1fGB" % last_sum
        bucketBytesAxis.text(timeSeries.timeToKiloOp(last_t), last_sum, msg, horizontalalignment="right")
    except: pass

    def plotPivotRate(ax):
        ax.set_title("buckets per node")
        nodeTimes = list(e.scopes[".NodeImpl_Compile::Node"].keys())
        def nodeCountAt(t):
            idx = bisect.bisect(nodeTimes, t)
            t = nodeTimes[idx]
            return e.scopes[".NodeImpl_Compile::Node"][t]
        line, = ax.plot(*timeSeries.makePlot(e.accum["pivot-key-count"], lambda t: (e.accum["pivot-key-count"][t]+nodeCountAt(t).open_count)/nodeCountAt(t).open_count))
        line.set_label("buckets/node")
        ax.set_ylabel("buckets/node")
        ax.yaxis.set_major_locator(matplotlib.ticker.MultipleLocator(1.0))
        ax.yaxis.set_minor_locator(matplotlib.ticker.MultipleLocator(0.5))
        ax.grid(axis="y", which="both", b=True)

    try: plotPivotRate(timeSeries.nextOpAxis())
    except: pass

    def plotMemViews(ax):
        ax.set_title("all memory views in one place")
        ax.set_ylabel("GB")

        line, = ax.plot(*timeSeries.makePlot(e.os_map_total, lambda t: e.os_map_total[t]/GB))
        line.set_label("OS mapping")

        line, = ax.plot(*timeSeries.makePlot(e.kvl_underlying, lambda t: e.kvl_underlying[t]/GB))
        line.set_label("underlying")

        line, = ax.plot(*timeSeries.makePlot(e.microscopes["total"], lambda t: e.microscopes["total"][t].open_byte/GB))
        line.set_label("malloc total")

        line, = ax.plot(*timeSeries.makePlot(e.scopes["in_amass.[T = unsigned char]"], lambda t: e.scopes["in_amass.[T = unsigned char]"][t].open_byte/GB))
        line.set_label("malloc in_amass")

        line, = ax.plot(*timeSeries.makePlot(e.accum["bucket-message-bytes"], lambda t: e.accum["bucket-message-bytes"][t]/GB))
        line.set_label("internal-bucket-message-bytes")
        ax.legend()

    try: plotMemViews(timeSeries.nextOpAxis())
    except: pass


#    xs = [t for t in e.kvl_underlying]
#    ys = [e.kvl_underlying[t]/GB for t in xs]
#    line, = axes[4].plot(xs, ys)
#    line.set_label("underlying sum");
#    ys = [e.scopes["in_amass.[T = unsigned char]"][t].open_byte/GB for t in xs]
#    line, = axes[4].plot(xs, ys)
#    line.set_label("amass");
#    axes[4].legend()
#    axes[4].set_ylabel("GB")
#    axes[4].set_title("malloc amass vs underlying sum")
#
#    xs = [t for t in e.kvl_underlying_count]
#    ys = [e.kvl_underlying_count[t] for t in xs]
#    line, = axes[5].plot(xs, ys)
#    line.set_label("reachable underlying allocs")
#    ys = [e.scopes["in_amass.[T = unsigned char]"][t].open_count for t in xs]
#    line, = axes[5].plot(xs, ys)
#    line.set_label("amass live alloc count")
#    axes[5].legend()
#    axes[5].set_title("amass live allocs vs reachable underlying allocs")

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
#    dataset = e.microscopes["sfaLarge"]
#    cdf(axes[4], [dataset[t].open_byte for t in dataset])

#    xs_byteToMalloc = [t for t in xs_bytearys]
#    ys_byteToMalloc = [ e.microscopes["total"][t].open_byte / focus_bytearys[t].open_byte for t in xs_byteToMalloc]
#    line, = axes[4].plot(xs_byteToMalloc, ys_byteToMalloc)
#    line.set_label("malloc total / bytes in byte[]")
#    axes[4].set_ylim(bottom = 0)
#    xs_mallocToOs = e.microscopes["total"].keys()
#    ys_mallocToOs = [e.os_map_total[t] / e.microscopes["total"][t].open_byte for t in xs_mallocToOs]
#    line, = axes[4].plot(xs_mallocToOs, ys_mallocToOs)
#    line.set_label("OS mapping / malloc total")
#    axes[4].legend()
#    axes[4].set_title("overheads")

    plotHelper.save("%s-timeseries.png" % e.filename)
    
plot_memory_timeseries(Experiment(sys.argv[1]))
