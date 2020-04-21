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

    plotHelper = PlotHelper(10)
    #timeSeries = TimeSeries(exp, plotHelper)

    def plotThroughput(ax):
        ax.set_title("op throughput")
        #ax.set_ylabel("Kops/sec")
        line, = ax.plot(*plotVsKop(ax, exp, windowedPair(ax, exp.operation, exp.elapsed, scale=K)))
        ax.plot(*plotVsKop(ax, exp, windowedPair(ax, exp.operation, exp.elapsed, window=1000*K(), scale=K)))
        line.set_label("tput")
        ax.legend(loc="lower left")
        ax.set_yscale("log")
        ax.set_ylim(bottom=0.1)
        ax.grid(which="major", color="black")
        ax.grid(which="minor", color="#dddddd")
        
        for phase,opn in exp.phase_starts.items():
            #print (phase,opn)
            ax.text(opn/K(), 0, phase)

        a2 = ax.twinx()
        def elapsedTime(opn):
            return exp.elapsed[opn]
        line, = a2.plot(*plotVsKop(ax, exp, elapsedTime), color="green")
        line.set_label("elapsed")
        a2.set_ylabel("s")
        a2.legend(loc="center right")

    try:
        plotThroughput(plotHelper.nextAxis(depth=2))
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

    def plotMemory(ax):
        line, = ax.plot(*plotVsKop(ax, exp, singleTrace(ax, exp.os_map_total, scale=Gi)))
        line.set_label("OS mem")
        ax.legend()
    plotMemory(plotHelper.nextAxis())

    def plotCpuTime(ax):
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

    def plotVeriInternalMem(ax):
        ax.set_title("mem from inside veri")
        ax.set_ylim(bottom=0)
        traceNames = ["bucket-message-bytes", "bucket-key-bytes", "pivot-key-bytes"]
        for stackc in list(range(len(traceNames)))[::-1]:
            stack = [exp.accum[n] for n in traceNames[:stackc+1]]
            stackedTraces = StackedTraces(stack)
            line, = ax.plot(*plotVsKop(ax, exp, singleTrace(ax, stackedTraces, scale=Gi)))
            line.set_label(("" if stackc==0 else "+") + traceNames[stackc])
        ax.legend()
    try: plotVeriInternalMem(plotHelper.nextAxis())
    except: pass

    def plotProcIoBytes(ax):
        ax.set_title("proc io bytes")
        window = 100*K()
        line, = ax.plot(*plotVsKop(ax, exp, windowedPair(ax, exp.procio_read_bytes, exp.operation, scale=Ki, window=window)))
        line.set_label("read")
        line, = ax.plot(*plotVsKop(ax, exp, windowedPair(ax, exp.procio_write_bytes, exp.operation, scale=Ki, window=window)))
        line.set_label("write")
        ax.legend()
    try: plotProcIoBytes(plotHelper.nextAxis())
    except: raise
    
    ########################################
    plotHelper.save("%s-perf.png" % exp.filename)

plot_perf_timeseries(Experiment(sys.argv[1]))
