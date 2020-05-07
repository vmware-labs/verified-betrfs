#!/usr/bin/env python3
import matplotlib
import matplotlib.pyplot as plt
import numpy as np
import sys
import operator
import bisect
import os
from parser import Experiment
from PlotHelper import *
from TimeSeries import *

def plot_perf_timeseries(exp):
    """exp: Experiment"""

    plotHelper = PlotHelper(12, scale=1.5)
    exp.nickname = ""   # this is a single exp; don't clutter legends

    try:
        plotThroughput(plotHelper.nextAxis(depth=2), [exp])
    except: raise

    class IOMode:
        def __init__(self, label):
            self.label = label
            self.count_source = exp.read_count if label=="read" else exp.write_count
            self.byte_source = exp.read_bytes if label=="read" else exp.write_bytes
    read_mode = IOMode("read")
    write_mode = IOMode("write")

    def plotIORate(ax, iomode):
        ax.set_title("io per opn -- %s" % iomode.label)
        line, = ax.plot(*plotVsKop(ax, exp, windowedPair(ax, iomode.count_source, exp.operation, scale=Unit)), "red")
        line.set_label(iomode.label)
        ax.legend()

        a2 = ax.twinx()
        xs,ys = plotVsKop(a2, exp, windowedPair(a2, iomode.byte_source, iomode.count_source, scale=Mi))
        line, = a2.plot(xs, ys)
        line.set_label(iomode.label)
        a2.legend(loc="lower right")
        if len(ys)>0:
            a2.set_ylim(bottom=0, top=ys[-1]*1.5)

    try:
        plotIORate(plotHelper.nextAxis(), read_mode)
        plotIORate(plotHelper.nextAxis(), write_mode)
    except: raise


    def plotIOAgainstTime(ax, iomode):
        ax.set_title("io per time -- %s" % iomode.label)
        line, = ax.plot(*plotVsKop(ax, exp, windowedPair(ax, iomode.count_source, exp.elapsed, scale=Unit)), "red")
        line.set_label(iomode.label)
        ax.legend()

        a2 = ax.twinx()
        line, = a2.plot(*plotVsKop(a2, exp, windowedPair(a2, iomode.byte_source, exp.elapsed, scale=Mi)))
        line.set_label(iomode.label)
        a2.legend(loc="lower right")

    plotIOAgainstTime(plotHelper.nextAxis(), read_mode)
    plotIOAgainstTime(plotHelper.nextAxis(), write_mode)

    def plotCacheEstimates(ax):
        ax.set_title("data set size")
        scale = Gi
        def writeCountEstimate(opn):
            #workload a
            assume_initialRecords = 1e6 # already wrong. Read from wkld file?
            assume_writeFraction = 0.5
            return opn*assume_writeFraction + assume_initialRecords
        def dataSizeEstimate(opn):
            assume_keySize = 24
            assume_valueSize = 512
            return writeCountEstimate(opn) * (assume_keySize + assume_valueSize) / scale()
        line, = ax.plot(*plotVsKop(ax, exp, dataSizeEstimate))
        line.set_label("data stored")
        ax.set_ylabel("%sB" % scale)
        ax.set_ylim(bottom=0)
        ax.legend()
#    try: plotCacheEstimates(plotHelper.nextAxis())
#    except: raise

    plotGrandUnifiedMemory(plotHelper.nextAxis(depth=2), [exp])

    def plotCpuTime(ax):
        ax.set_title("CPU time")
        ticksPerSecond = os.sysconf(os.sysconf_names['SC_CLK_TCK'])
        user_sec = LambdaTrace(lambda opn: exp.utime[opn]/ticksPerSecond, "s")
        sys_sec = LambdaTrace(lambda opn: exp.stime[opn]/ticksPerSecond, "s")

        #print("ticksPerSecond", ticksPerSecond)
        line, = ax.plot(*plotVsKop(ax, exp, windowedPair(ax, user_sec, exp.elapsed)))
        line.set_label("user")
        line, = ax.plot(*plotVsKop(ax, exp, windowedPair(ax, sys_sec, exp.elapsed)))
        line.set_label("sys")
        ax.legend()
    plotCpuTime(plotHelper.nextAxis())

# Moved to Grand Unified
#    def plotVeriInternalMem(ax):
#        ax.set_title("mem from inside veri")
#        traceNames = ["bucket-message-bytes", "bucket-key-bytes", "pivot-key-bytes"]
#        def StackFor(count):
#            return [exp.accum[n] for n in traceNames[:count+1]]
#
#        def plotWithLabel(lam, lbl, **plotkwargs):
#            xs,ys = plotVsKop(ax, exp, lam)
#            line, = ax.plot(xs, ys, **plotkwargs)
#            line.set_label(lbl + (" %.2f%sB" % (ys[-1], Gi.prefix)))
#
#        for stackc in list(range(len(traceNames)))[::-1]:
#            stack = StackFor(stackc)
#            stackedTraces = StackedTraces(stack)
#            plotWithLabel(singleTrace(ax, stackedTraces, scale=Gi),
#                    ("" if stackc==0 else "+") + traceNames[stackc])
#
#        plotWithLabel(singleTrace(ax, exp.jem_allocated, scale=Gi), "jem_allocated", linestyle="dotted")
#
#        def annotate_overhead():
#            stackedTraces = StackedTraces(StackFor(len(traceNames)))
#            xs,ys = plotVsKop(ax, exp, singleTrace(ax, stackedTraces, scale=Gi))
#            total_last = ys[-1]
#            xs,ys = plotVsKop(ax, exp, singleTrace(ax, exp.jem_allocated, scale=Gi))
#            jem_last = ys[-1]
#            ax.text(xs[-1], ys[-1], "%.2fX" % (jem_last/total_last))
#        annotate_overhead()
#
#        ax.legend()
#        ax.set_ylim(bottom=0)
#    try: plotVeriInternalMem(plotHelper.nextAxis())
#    except: pass

    def plotProcIoBytes(ax):
        ax.set_title("proc io bytes")
        window = 100*K()
        line, = ax.plot(*plotVsKop(ax, exp, windowedPair(ax, exp.procio_read_bytes, exp.operation, scale=Ki, window=window)), color="green")
        line.set_label("read")
        line, = ax.plot(*plotVsKop(ax, exp, windowedPair(ax, exp.procio_write_bytes, exp.operation, scale=Ki, window=window)), color="orange")
        line.set_label("write")

        rio_bytes = LambdaTrace(lambda opn: exp.rocks_io_reads[opn]*4096, "B")
#        line, = ax.plot(*plotVsKop(ax, exp, windowedPair(ax, rio_bytes, exp.operation, scale=Ki, window=window)))
#        line.set_label("rio_access")

        miss_bytes = LambdaTrace(lambda opn: (exp.rocks_io_reads[opn] - exp.rocks_io_hits[opn])*4096, "B")
        line, = ax.plot(*plotVsKop(ax, exp, windowedPair(ax, miss_bytes, exp.operation, scale=Ki, window=window)), linestyle="dotted", color="green")
        line.set_label("rio_miss")

        miss_bytes = LambdaTrace(lambda opn: (exp.rocks_io_reads[opn])*4096, "B")
        line, = ax.plot(*plotVsKop(ax, exp, windowedPair(ax, miss_bytes, exp.operation, scale=Ki, window=window)), linestyle="dotted", color="blue")

        line.set_label("rio_read")

        miss_bytes = LambdaTrace(lambda opn: (exp.rocks_io_writes[opn])*4096, "B")
        line, = ax.plot(*plotVsKop(ax, exp, windowedPair(ax, miss_bytes, exp.operation, scale=Ki, window=window)), linestyle="dotted", color="black")
        line.set_label("rio_write")

        ax.legend()
    try: plotProcIoBytes(plotHelper.nextAxis(depth=2))
    except: raise

    def plotRocksIo(ax):
        ax.set_title("rocks io")
        window = 10*K()

        hit_ratio = LambdaTrace(lambda opn: exp.rocks_io_hits[opn]/exp.rocks_io_reads[opn], "frac")
        line, = ax.plot(*plotVsKop(ax, exp, windowedPair(ax, exp.rocks_io_hits, exp.rocks_io_reads, window=window)))
        line.set_label("rio_ratio")
        line, = ax.plot(*plotVsKop(ax, exp, windowedPair(ax, exp.rocks_io_hits, exp.rocks_io_reads, window=100*window)), linestyle="dotted")
#        line, = ax.plot(*plotVsKop(ax, exp, windowedPair(ax, exp.rocks_io_reads, exp.operation, window=window)))
#        line.set_label("rio_access")

        miss_pages = LambdaTrace(lambda opn: (exp.rocks_io_reads[opn] - exp.rocks_io_hits[opn]), "pages")
        line, = ax.plot(*plotVsKop(ax, exp, windowedPair(ax, miss_pages, exp.operation, scale=Unit)))
        line.set_label("miss_per_opn (%s)" % miss_pages.units)


        ax.set_ylim(bottom=0)
        ax.legend()

    plotRocksIo(plotHelper.nextAxis())

    def plotPgfault(ax):
        ax.set_title("cgroups-stat-pgfault")
        trace = exp.cgroups_stat["pgfault"]
        line, = ax.plot(*plotVsKop(ax, exp, windowedPair(ax, trace, exp.operation, scale=Unit)), "red")
        line.set_label(trace.label)
        ax.legend()
#    try: plotPgfault(plotHelper.nextAxis())
#    except: raise
    
    ########################################
    plotHelper.save("%s-perf.png" % exp.filename)

plot_perf_timeseries(Experiment(sys.argv[1]))
