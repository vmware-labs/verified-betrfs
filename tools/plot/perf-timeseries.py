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

def plot_perf_timeseries(exp):
    """exp: Experiment"""

    plotHelper = PlotHelper(4)
    #timeSeries = TimeSeries(exp, plotHelper)

    def plotVsKop(ax, lam):
        # ax: which axis to apply the x-label to
        # lam(opn): compute a y value for a given opn value
        # returns xs,ys suitable to be passed to plt.plot
        ax.set_xlabel("op num (K)")
        ax.set_xlim(left = 0, right=exp.op_max/Kilo)
        xs = []
        ys = []
        for opn in exp.sortedOpns:
            try:
                x = opn/Kilo
                y = lam(opn)
                if x!=None and y != None:
                    xs.append(x)
                    ys.append(y)
            except KeyError: pass
            except IndexError: pass
        assert None not in xs
        assert None not in ys
        return xs,ys

    def windowedRate(trace, window, scale=1.0, reciprocal=False):
        def val(opn):
            opnBefore = opn - window
            if opnBefore < 0:
                return None
            vAfter = trace[opn]
            vBefore = trace[opnBefore]
            if vAfter == vBefore:
                return None
            rate = (vAfter - vBefore) / (opn - opnBefore)
            if reciprocal:
                rate = 1.0 / rate
            return rate / scale
        return val

    def plotThroughput(ax):
        ax.set_title("op throughput")
        ax.set_ylabel("Kops/sec")
        line, = ax.plot(*plotVsKop(ax, windowedRate(exp.elapsed, 100*Kilo, reciprocal=True)))
        ax.plot(*plotVsKop(ax, windowedRate(exp.elapsed, 1000*Kilo, reciprocal=True)))
        line.set_label("tput")
        ax.legend(loc="lower left")

        a2 = ax.twinx()
        def elapsedTime(opn):
            return exp.elapsed[opn]
        line, = a2.plot(*plotVsKop(ax, elapsedTime), color="green")
        line.set_label("elapsed")
        a2.legend(loc="center right")

    try:
        plotThroughput(plotHelper.nextAxis())
    except: raise

    def plotIORate(ax, iotype):
        ax.set_title("io rate -- %s" % iotype)

        count_source = exp.read_count if iotype=="read" else exp.write_count
        byte_source = exp.read_bytes if iotype=="read" else exp.write_bytes

        line, = ax.plot(*plotVsKop(ax, windowedRate(count_source, 100*Kilo)),
                    color="red")
        line.set_label("IO/opn")

        ax.set_ylim(bottom=0)
        ax.set_ylabel("IOs/operation")
        ax.legend(loc="upper left")

        a2 = ax.twinx()
        # Can't use smooth() because we need to examine both sides of the
        # window before dividing. That, and we don't want
        # bytes-per-IO-per-op-completed.
        def bytesPerIO(opn):
            window = 100*Kilo
            opnBefore = opn - window
            if opnBefore < 0:
                return None
            bytes = byte_source[opn] - byte_source[opnBefore]
            count = count_source[opn] - count_source[opnBefore]
            result = bytes/count/MB if count>0 else 0
            return result

        xs,ys = plotVsKop(ax, bytesPerIO)
        line, = a2.plot(xs, ys)
        line.set_label("MB/IO")
        cur =  ys[-1] if len(ys)>0 else 0
        a2.set_ylabel("MB/IO")
        a2.legend(loc="lower right")
        a2.set_ylim(bottom=0, top=cur*2)
    try:
        plotIORate(plotHelper.nextAxis(), "read")
        plotIORate(plotHelper.nextAxis(), "write")
    except: raise

    def plotCacheEstimates(ax):
        ax.set_title("data set size")
        def writeCountEstimate(opn):
            #workload a
            assume_initialRecords = 1e6
            assume_writeFraction = 0.5
            return opn*assume_writeFraction + assume_initialRecords
        def dataSizeEstimate(opn):
            assume_keySize = 24
            assume_valueSize = 512
            return writeCountEstimate(opn) * (assume_keySize + assume_valueSize) / GB
        line, = ax.plot(*plotVsKop(ax, dataSizeEstimate))
        line.set_label("data stored (GB)")
        ax.set_ylim(bottom=0)
        ax.legend()
    try:
        plotCacheEstimates(plotHelper.nextAxis())
    except: pass

    plotHelper.save("%s-perf.png" % exp.filename)
    
plot_perf_timeseries(Experiment(sys.argv[1]))
