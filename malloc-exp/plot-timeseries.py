#!/usr/bin/env python3
import matplotlib
import matplotlib.pyplot as plt
import numpy as np
import re
import sys
import operator
import bisect

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
    reads_started = {}
    reads_completed = {}
    writes_started = {}
    writes_completed = {}
    scopes = {}
    kvl_underlying = {}
    kvl_underlying_count = {}
    accum = {}
    line_num = 0
    for line in open(filename, "r").readlines():
        line_num += 1
        line = line.strip()
        fields = line.split()

        if line.startswith("veribetrkv [op] sync") or line.startswith("rocksdb [op] sync"):
            if first_op_completed_t == None:
                first_op_completed_t = t - 2
            ops_completed[t] = int(fields[4])
            t += 1

        if line.startswith("os-map-total"):
            os_map_total[t] = int(fields[1])
            os_map_heap[t] = int(fields[3])

        if line.startswith("iostats "):
            reads_started[t] = int(fields[1])
            reads_completed[t] = int(fields[3])
            writes_started[t] = int(fields[5])
            writes_completed[t] = int(fields[7])

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


        mo = re.compile("cache: (\d+) (.*)-(bytes|count)").search(line)
        if mo!=None:
            value,type,unit = mo.groups()
            accum_key = "%s-%s" % (type,unit)
            if accum_key not in accum:
                accum[accum_key] = {}
            accum[accum_key][t] = int(value)

    numPlots = 10
    rows = int((numPlots+1)/2)
    fig, axes = plt.subplots(rows, 2, figsize=(12,rows*2))
    axes = axes.transpose().flatten()
    plt.subplots_adjust(left=0.10, right=0.90, hspace=0.4, top=0.95, bottom=0.05);

    class AxisAllocator:
        def __init__(self):
            self.nextAxis = 0

        def get(self):
            ret = self.nextAxis
            self.nextAxis += 1
            return axes[ret]
    axisAllocator = AxisAllocator()

    t_end = max(ops_completed.keys())

    Kilo = 1000
    MB = float(1<<20)
    GB = float(1<<30)

    def timeToOp(t):
        try:
            return ops_completed[t]
        except KeyError:
            return 0

    opValues = list(ops_completed.values())
    opValues.sort()
    opTimes = list(ops_completed.keys())
    opTimes.sort()
    def opToTime(op):
        idx = bisect.bisect(opValues, op)
        return opTimes[idx]

    def timeToKiloOp(t):
        return timeToOp(t) / Kilo

    def timesToKiloOps(ts):
        return [timeToKiloOp(t) for t in ts]

    op_end = timeToKiloOp(t_end)

    def makePlot(xSource, lam):
        xs = []
        ys = []
        for t in xSource:
            try:
                y = lam(t)
                if y != None:
                    xs.append(t)
                    ys.append(y)
            except KeyError: pass
            except IndexError: pass
        return timesToKiloOps(xs),ys


    def smoothedThroughput(ax, window):
        xs,ys = makePlot(ops_completed, lambda t: (ops_completed[t] - ops_completed[t-window])/float(window)/Kilo)
        ax.plot(xs, ys)
        return ys[-1]

    def plotThroughput(ax):
        ax.set_title("op throughput")
        smoothedThroughput(ax, 10)
        cur = smoothedThroughput(ax, 100)
        ax.set_xlim(left = 0, right=op_end)
        ax.set_ylim(bottom = 0)
        ax.set_ylabel("Kops/sec")
        ax.set_xlabel("op num (K)")

        xs = [t for t in ops_completed]
        def aggregateAt(time, label):
            if time > xs[-1]:
                return
            aggregate = (ops_completed[time] - ops_completed[xs[0]])/float(time-xs[0])/Kilo
            msg = "mean %.1f" % aggregate
            if label == "end":
                msg += "\ncur %.2f" % cur
            ax.text(timeToKiloOp(time), aggregate, msg, horizontalalignment="right")
        aggregateAt(xs[-1], "end")
        t1m = opToTime(2000000)
        aggregateAt(t1m, "op1000k")
        
        axtwin = ax.twinx()
        ts = [t for t in ops_completed]
        ops = [ops_completed[t]/Kilo for t in xs]
        axtwin.plot(ops,ts, "g")
        axtwin.set_ylabel("time (s)")

    try: plotThroughput(axisAllocator.get())
    except: raise

    def plotOSvsMalloc(ax):
        try:
            line, = ax.plot(*makePlot(microscopes["total"], lambda t: microscopes["total"][t].open_byte/GB))
            line.set_label("malloc total")
            line, = ax.plot(*makePlot(microscopes["coarse-small"], lambda t: microscopes["coarse-small"][t].open_byte/GB))
            line.set_label("malloc small")
            line, = ax.plot(*makePlot(microscopes["coarse-small"], lambda t:
                (microscopes["coarse-small"][t].open_byte + microscopes["coarse-large"][t].open_byte)/GB))
            line.set_label("malloc large")
        except:
            pass    # sorry, no microscopes
        line, = ax.plot(*makePlot(os_map_total, lambda t: os_map_total[t]/GB))
        line.set_label("OS mapping")
        line, = ax.plot(*makePlot(os_map_heap, lambda t: os_map_heap[t]/GB))
        line.set_label("OS heap mapping")

        maxX, maxY = max(os_map_total.items(), key=operator.itemgetter(1))
        ax.text(timeToKiloOp(maxX), maxY/GB, "max %.1fGB" % (maxY/GB), horizontalalignment="right")

        ax.set_xlim(left = 0, right=op_end)
        ax.legend()
        ax.set_title("allocations")
        ax.set_ylabel("GB")
    osVsMallocAxis = axisAllocator.get()
    try: plotOSvsMalloc(osVsMallocAxis)
    except: pass

    def plotAmass(ax):
        focus_bytearys = scopes["in_amass.[T = unsigned char]"]
        line, = ax.plot(*makePlot(focus_bytearys, lambda t: focus_bytearys[t].open_byte/GB), linestyle="dotted")
        line.set_label("in_amass");
        ax.set_ylabel("GB")
        ax.legend()
        ax.set_xlim(left = 0, right=op_end)
    try: plotAmass(osVsMallocAxis)
    except: pass

    def plotNodes(ax):
        a2twin = ax.twinx()
        a2twin.set_ylabel("count")

        focus_bytearys = scopes["in_amass.[T = unsigned char]"]
        line, = a2twin.plot(*makePlot(focus_bytearys, lambda t: focus_bytearys[t].open_count))
        line.set_label("[byte] count");

        focus_nodes = scopes[".NodeImpl_Compile::Node"]
        line, = a2twin.plot(*makePlot(focus_nodes, lambda t: focus_nodes[t].open_count))
        line.set_label("Node count")
        line, = a2twin.plot(*makePlot(microscopes["sfaLarge"], lambda t: microscopes["sfaLarge"][t].open_count))
        line.set_label("amass count")
        line, = a2twin.plot(*makePlot(microscopes["esLarge"], lambda t: microscopes["esLarge"][t].open_count))
        line.set_label("pagein count")
        a2twin.legend(loc="lower left")

    amassAxis = axisAllocator.get()
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
                  (microscopes["esLarge"], "pagein"),
                  (microscopes["sfaLarge"], "amass"),
                  (scopes["in_amass.[T = unsigned char]"], "in_amass"),
                ]
        xs = [t for t in stack[0][0]]
        prev = [0 for t in xs]
        for i in range(len(stack)):
            (item,label) = stack[i]
            ys = [(item[xs[i]].open_byte + prev[i]) for i in range(len(xs))]
            line, = ax.plot(timesToKiloOps(xs), [v/GB for v in ys])
            line.set_label(label)
            prev = ys
            #prev = [0 for t in xs]
        line, = ax.plot(timesToKiloOps(xs), [microscopes["total"][t].open_byte/GB for t in xs])
        line.set_label("malloc total")
        ax.legend()
        ax.set_ylabel("GB")
        ax.set_xlim(left = 0, right=op_end)
        ax.grid(axis="y", which="both", b=True)
    try: plotMemStackChart(axisAllocator.get())
    except: pass

    def plotIORate(completed, label, color, ax):
        window = 20
        def windowedIO(completed, t):
            try:
                op_t = timeToOp(t)
                op_window = timeToOp(t - window)
                if op_window >= op_t:
                    return None
                #print(t, started[t], completed[t-window], op_t, op_window)
                return (completed[t] - completed[t-window])/(op_t - op_window)
            except ZeroDivisionError:
                return None
        line, = ax.plot(*makePlot(completed, lambda t: windowedIO(completed, t)), color=color)
        line.set_label(label)
        ax.set_title("IOs per operation, %ss window" % window)
        ax.legend()
        #ax.set_ylim(top=0.15)
        
    ioRateAxis = axisAllocator.get()
    try:
        #axtwin = axes[4].twinx()
        plotIORate(writes_completed, "writes", "b", ioRateAxis)
        plotIORate(reads_completed, "reads", "r", ioRateAxis)
    except: raise

    def plotAccum(ax, accum_suite, divisor, ylabel):
        for categ in accum_suite:
            line, = ax.plot(*makePlot(accum[categ], lambda t: accum[categ][t]/divisor))
            line.set_label(categ)
        ax.set_title("internal accumulator")
        ax.set_ylabel(ylabel)
        ax.legend()

    try:
        plotAccum(axisAllocator.get(), ("tree-nodes-count", "tree-buckets-count", "pkv-buckets-count", "weird-buckets-count"), 1, "count")
        plotAccum(axisAllocator.get(), ("bucket-message-count", "bucket-key-count", "pivot-key-count"), 1e6, "M")
        bucketBytesAxis = axisAllocator.get()
        plotAccum(bucketBytesAxis, ("bucket-message-bytes", "bucket-key-bytes", "pivot-key-bytes"), GB, "GB")
        last_t = max(accum["bucket-message-bytes"].keys())
        last_sum = sum([accum[c][last_t] for c in ["bucket-message-bytes", "bucket-key-bytes", "pivot-key-bytes"]])/GB
        msg = "total: %.1fGB" % last_sum
        bucketBytesAxis.text(timeToKiloOp(last_t), last_sum, msg, horizontalalignment="right")
    except: pass

    def plotPivotRate(ax):
        ax.set_title("buckets per node")
        nodeTimes = list(scopes[".NodeImpl_Compile::Node"].keys())
        def nodeCountAt(t):
            idx = bisect.bisect(nodeTimes, t)
            t = nodeTimes[idx]
            return scopes[".NodeImpl_Compile::Node"][t]
        line, = ax.plot(*makePlot(accum["pivot-key-count"], lambda t: (accum["pivot-key-count"][t]+nodeCountAt(t).open_count)/nodeCountAt(t).open_count))
        line.set_label("buckets/node")
        ax.set_ylabel("buckets/node")
        ax.yaxis.set_major_locator(matplotlib.ticker.MultipleLocator(1.0))
        ax.yaxis.set_minor_locator(matplotlib.ticker.MultipleLocator(0.5))
        ax.grid(axis="y", which="both", b=True)

    try: plotPivotRate(axisAllocator.get())
    except: pass

    def plotMemViews(ax):
        ax.set_title("all memory views in one place")
        ax.set_ylabel("GB")

        line, = ax.plot(*makePlot(os_map_total, lambda t: os_map_total[t]/GB))
        line.set_label("OS mapping")

        line, = ax.plot(*makePlot(kvl_underlying, lambda t: kvl_underlying[t]/GB))
        line.set_label("underlying")

        line, = ax.plot(*makePlot(microscopes["total"], lambda t: microscopes["total"][t].open_byte/GB))
        line.set_label("malloc total")

        line, = ax.plot(*makePlot(scopes["in_amass.[T = unsigned char]"], lambda t: scopes["in_amass.[T = unsigned char]"][t].open_byte/GB))
        line.set_label("malloc in_amass")

        line, = ax.plot(*makePlot(accum["bucket-message-bytes"], lambda t: accum["bucket-message-bytes"][t]/GB))
        line.set_label("internal-bucket-message-bytes")
        ax.legend()

    try: plotMemViews(axisAllocator.get())
    except: pass


#    xs = [t for t in kvl_underlying]
#    ys = [kvl_underlying[t]/GB for t in xs]
#    line, = axes[4].plot(xs, ys)
#    line.set_label("underlying sum");
#    ys = [scopes["in_amass.[T = unsigned char]"][t].open_byte/GB for t in xs]
#    line, = axes[4].plot(xs, ys)
#    line.set_label("amass");
#    axes[4].legend()
#    axes[4].set_ylabel("GB")
#    axes[4].set_title("malloc amass vs underlying sum")
#
#    xs = [t for t in kvl_underlying_count]
#    ys = [kvl_underlying_count[t] for t in xs]
#    line, = axes[5].plot(xs, ys)
#    line.set_label("reachable underlying allocs")
#    ys = [scopes["in_amass.[T = unsigned char]"][t].open_count for t in xs]
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

    plt.tight_layout()
    figname = "%s-timeseries.png" % filename
    plt.savefig(figname)
    #plt.show()
    
parse(sys.argv[1])
