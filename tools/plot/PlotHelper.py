#!/usr/bin/env python3
import matplotlib
import matplotlib.pyplot as plt
from matplotlib.gridspec import GridSpec
import numpy as np
import sys
import operator
import bisect
import os


class Scale:
    def __init__(self, prefix, mult):
        self.prefix = prefix
        self.mult = float(mult)

    def __call__(self):
        return self.mult

    def __repr__(self):
        return self.prefix

Unit = Scale("", 1)
K = Scale("K", 1000)
Ki = Scale("Ki", 1024)
Mi = Scale("Mi", 1<<20)
Gi = Scale("Gi", 1<<30)

class PlotHelper:
    def __init__(self, numPlots, scale=1, columns=None):
        self.numPlots = numPlots
        if columns:
            self.columns = columns
        else:
            self.columns = 2 if numPlots > 4 else 1
        self.rows = int((numPlots+0.5)/self.columns)
        # You may need: sudo pip3 install --upgrade matplotlib
        self.fig = plt.figure(#constrained_layout=True,
                    figsize = (scale*7*self.columns, scale*self.rows*2))
        self.gridspec = GridSpec(self.rows, self.columns)
        #self.fig, self.axes = plt.subplots(rows, columns, figsize=())
        #self.axes = self.axes.transpose().flatten()
        plt.subplots_adjust(left=0.06, right=0.94, hspace=0.6, top=0.95, bottom=0.05);

        self.nextAxisSlot = 0

    def nextAxis(self, depth=1):
        startSpot = self.nextAxisSlot
        self.nextAxisSlot += depth
        col = int(startSpot / self.rows)
        row = int(startSpot % self.rows)
        endRow = row + depth
        return self.fig.add_subplot(self.gridspec[row:endRow, col])

    def save(self, figname):
        #plt.tight_layout()
        plt.savefig(figname)

class LambdaTrace:
    """Wrap a trace in a function."""
    def __init__(self, lam, units):
        self.lam = lam
        self.units = units

    def __getitem__(self, opn):
        return self.lam(opn)

class StackedTraces:
    """Sum a set of traces."""
    def __init__(self, traces):
        self.traces = traces
        self.units = traces[0].units

    def __getitem__(self, opn):
        return sum([tr[opn] for tr in self.traces])

def plotVsKop(ax, exp, lam, debug=False):
    # ax: which axis to apply the x-label to
    # lam(opn): compute a y value for a given opn value
    # returns xs,ys suitable to be passed to plt.plot
    ax.set_xlabel("op num (K)")
    ax.set_xlim(left = 0, right=exp.op_max/K())
    xs = []
    ys = []
    for opn in exp.sortedOpns:
        try:
            x = opn/K()
            y = lam(opn)
            if x!=None and y != None:
                xs.append(x)
                ys.append(y)
            elif debug:
                print (x, y)
        except KeyError:
            if debug: raise
            else: pass
        except IndexError:
            if debug: raise
            else: pass
    assert None not in xs
    assert None not in ys
    return xs,ys

def windowedPair(ax, num_trace, denom_trace, scale=Unit, window=100*K()):
    ax.set_ylabel("%s%s/%s" % (scale, num_trace.units, denom_trace.units))
    def val(opn):
        opnBefore = opn - window
        #if opnBefore < 0: return None
        try:
            num = num_trace[opn] - num_trace[opnBefore]
            denom = denom_trace[opn] - denom_trace[opnBefore]
        except TypeError:   # None because some opn isn't defined
            return None
        if denom == 0:
            return None
        rate = num/scale()/denom
        return rate
    return val

def singleTrace(ax, trace, scale=Unit):
    ax.set_ylabel("%s%s" % (scale, trace.units))
    def lam(opn):
        try:
            return trace[opn]/scale()
        except TypeError:   # None because trace undefined at opn
            return None
    return lam

def set_xlim(ax, experiments):
    xlim_right = 0
    for exp in experiments:
        xlim_right = max(xlim_right, exp.op_max/K())
    ax.set_xlim(left = 0, right=xlim_right)

spectrum = ["black", "brown", "red", "orange", "green", "indigo", "blue", "violet"]

def plotThroughput(ax, experiments):
    ax.set_title("op throughput")
    a2 = ax.twinx()
    a2.set_ylabel("s")
    for expi in range(len(experiments)):
        exp = experiments[expi]
        line, = ax.plot(*plotVsKop(ax, exp, windowedPair(ax, exp.operation, exp.elapsed, scale=K)), color=spectrum[expi])
        line.set_label(exp.nickname + " tput")
        ax.plot(*plotVsKop(ax, exp, windowedPair(ax, exp.operation, exp.elapsed, window=1000*K(), scale=K)), color=spectrum[expi], linestyle="dotted")

        def elapsedTime(opn):
            return exp.elapsed[opn]
        line, = a2.plot(*plotVsKop(ax, exp, elapsedTime), color=spectrum[expi])
        line.set_label(exp.nickname + " rate")
    ax.legend(loc="upper center")
    ax.set_yscale("log")
    ax.set_ylim(bottom=0.1)
    ax.grid(which="major", color="black")
    ax.grid(which="minor", color="#dddddd")
    set_xlim(ax, experiments)
    a2.legend(loc="lower center")
    
    for phase,opn in experiments[0].phase_starts.items():
        #print (phase,opn)
        ax.text(opn/K(), 0, phase)

def plotGrandUnifiedMemory(ax, experiments):
    ax.set_title("Grand Unified Memory")

    linestyles=["solid", "dashed", "dotted", "-."]
    coloridx = [0]
    def plotOneExp(exp, plotkwargs):
        labelidx = [0]
        plotkwargs["color"] = spectrum[coloridx[0] % len(spectrum)]
        coloridx[0] += 1

        def plotWithLabel(lam, lbl):
            plotkwargs["linestyle"] = linestyles[labelidx[0] % len(linestyles)]
            #print("using color %s for label %s" % (plotkwargs["color"], lbl))
            labelidx[0] += 1
            xs,ys = plotVsKop(ax, exp, lam)
            if len(xs)==0:
                # don't clutter legendspace
                return
            line, = ax.plot(xs, ys, **plotkwargs)
            line.set_label(lbl + (" %.2f%sB" % (ys[-1], Gi.prefix)))

        plotWithLabel(singleTrace(ax, exp.os_map_total, scale=Gi),
                exp.nickname + " OS mem")
        plotWithLabel(singleTrace(ax, exp.os_map_heap, scale=Gi),
                exp.nickname + " OS heap")
        plotWithLabel(singleTrace(ax, exp.cgroups_memory_usage_bytes, scale=Gi),
                exp.nickname + " cgroups-usage")

        # malloc & jemalloc
        plotWithLabel(singleTrace(ax, exp.jem_mapped, scale=Gi),
                exp.nickname + " jem mapped")
#        plotWithLabel(singleTrace(ax, exp.jem_active, scale=Gi),
#                exp.nickname + " jem active")
        plotWithLabel(singleTrace(ax, exp.jem_allocated, scale=Gi),
                exp.nickname + " jem alloc")

        mallocLam = singleTrace(ax, exp.microscopes["total"].getTrace("open_byte"), scale=Gi) if "total" in exp.microscopes else lambda opn: None
        plotWithLabel(mallocLam, exp.nickname + " malloc")

        # "underlying" view: measured in C++ below Dafny but above malloc
        plotWithLabel(singleTrace(ax, exp.kvl_underlying, scale=Gi),
                exp.nickname + " underlying")

        # internal views, stacked
        traceNames = ["bucket-message-bytes", "bucket-key-bytes", "pivot-key-bytes"]
        def StackFor(count):
            return [exp.accum[n] for n in traceNames[:count+1]]

        # Just plot the sum of internal stuff
        try:
            stackedTraces = StackedTraces(StackFor(len(traceNames)))
            plotWithLabel(singleTrace(ax, stackedTraces, scale=Gi),
                exp.nickname + " internal-accum-bytes")
        except: pass

    for i in range(len(experiments)):
        exp = experiments[i]
        plotOneExp(exp, {"linestyle": linestyles[i % len(linestyles)]})

    ax.set_ylim(bottom=0)
    set_xlim(ax, experiments)
    ax.legend(loc="upper left")

def plotRocksIo(ax, experiments):
    ax.set_title("rocks io")
    window = 10*K()

    def plotOneExp(exp, plotkwargs):
        hit_ratio = LambdaTrace(lambda opn: exp.rocks_io_hits[opn]/exp.rocks_io_reads[opn], "frac")
        line, = ax.plot(*plotVsKop(ax, exp, windowedPair(ax, exp.rocks_io_hits, exp.rocks_io_reads, window=window)), **plotkwargs)
        line.set_label(exp.nickname + " rio_ratio")
        line, = ax.plot(*plotVsKop(ax, exp, windowedPair(ax, exp.rocks_io_hits, exp.rocks_io_reads, window=100*window)), linestyle="dotted", **plotkwargs)
    #        line, = ax.plot(*plotVsKop(ax, exp, windowedPair(ax, exp.rocks_io_reads, exp.operation, window=window)))
    #        line.set_label("rio_access")

        miss_pages = LambdaTrace(lambda opn: (exp.rocks_io_reads[opn] - exp.rocks_io_hits[opn]), "pages")
        line, = ax.plot(*plotVsKop(ax, exp, windowedPair(ax, miss_pages, exp.operation, scale=Unit, window=100*K())), **plotkwargs)
        line.set_label(exp.nickname + " miss_per_opn (%s)" % miss_pages.units)
        line, = ax.plot(*plotVsKop(ax, exp, windowedPair(ax, miss_pages, exp.operation, scale=Unit, window=1000*K())), linestyle="dotted", **plotkwargs)


    for i in range(len(experiments)):
        exp = experiments[i]
        plotkwargs = {"color": spectrum[i % len(spectrum)]}
        plotOneExp(exp, plotkwargs)

    ax.set_ylim(bottom=0)
    ax.legend()


def plotCpuTime(ax, experiments):
    ax.set_title("CPU time")

    def plotOneExp(exp, plotkwargs):
        ticksPerSecond = os.sysconf(os.sysconf_names['SC_CLK_TCK'])
        user_sec = LambdaTrace(lambda opn: exp.utime[opn]/ticksPerSecond, "s")
        sys_sec = LambdaTrace(lambda opn: exp.stime[opn]/ticksPerSecond, "s")

        #print("ticksPerSecond", ticksPerSecond)
        line, = ax.plot(*plotVsKop(ax, exp, windowedPair(ax, user_sec, exp.elapsed)), **plotkwargs)
        line.set_label(exp.nickname+" user")
        line, = ax.plot(*plotVsKop(ax, exp, windowedPair(ax, sys_sec, exp.elapsed)), **plotkwargs, linestyle="dotted")
        line.set_label(exp.nickname+" sys")

    for i in range(len(experiments)):
        exp = experiments[i]
        plotkwargs = {"color": spectrum[i % len(spectrum)]}
        plotOneExp(exp, plotkwargs)

    set_xlim(ax, experiments)
    ax.set_ylim(bottom=0)
    ax.legend()

def plotProcIoBytes(ax, experiments):
    ax.set_title("proc io bytes")

    def plotOneExp(exp, plotkwargs):
        window = 1000*K()
        line, = ax.plot(*plotVsKop(ax, exp, windowedPair(ax, exp.procio_read_bytes, exp.operation, scale=Ki, window=window)), **plotkwargs)
        line.set_label(exp.nickname + " read")
        line, = ax.plot(*plotVsKop(ax, exp, windowedPair(ax, exp.procio_write_bytes, exp.operation, scale=Ki, window=window)), linestyle="dotted", **plotkwargs)
        line.set_label(exp.nickname + " write")

    for i in range(len(experiments)):
        exp = experiments[i]
        plotkwargs = {"color": spectrum[i % len(spectrum)]}
        plotOneExp(exp, plotkwargs)

    ax.grid(which="major", color="#dddddd")
    set_xlim(ax, experiments)
    ax.set_ylim(bottom=0)
    ax.legend()
