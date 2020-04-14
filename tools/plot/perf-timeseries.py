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

def plot_perf_timeseries(e):
    """e: Experiment"""

    plotHelper = PlotHelper(4)
    timeSeries = TimeSeries(e, plotHelper)

    try: timeSeries.plotThroughput(timeSeries.nextOpAxis())
    except: pass

#    def plotIOCount(ax):
#        ax.set_title("io count")
#        line, = ax.plot(*timeSeries.makePlot(e.read_count, lambda t: e.read_count[t]))
#        line.set_label("read")
#        line, = ax.plot(*timeSeries.makePlot(e.write_count, lambda t: e.write_count[t]))
#        line.set_label("write")
#        ax.legend()
#    try: plotIOCount(timeSeries.nextOpAxis())
#    except: raise

    def plotIORate(ax, iotype):
        ax.set_title("io rate -- %s" % iotype)
        WINDOW = 50

        count_source = e.read_count if iotype=="read" else e.write_count
        byte_source = e.read_bytes if iotype=="read" else e.write_bytes


        lam = lambda t: count_source[t]
        #print(count_source)
        timeSeries.smooth(ax, window=WINDOW, source=count_source, fieldfunc=lam, divideBy=OpCount, label="IO/opn", color="red")
        ax.set_ylim(bottom=0)
        ax.set_ylabel("IOs/operation")
        ax.legend(loc="upper left")

        tx = ax.twinx()
        bytes_source = e.read_bytes if iotype=="read" else e.write_bytes
        lam = lambda t: bytes_source[t]/count_source[t] if count_source[t]>0 else 0

        # Can't use smooth() because we need to examine both sides of the
        # window before dividing. That, and we don't want
        # bytes-per-IO-per-op-completed.
        def bytesPerIO(t):
            bytes = byte_source[t] - byte_source[t-WINDOW]
            count = count_source[t] - count_source[t-WINDOW]
            result = bytes/count/MB if count>0 else 0
            return result
        xs,ys = timeSeries.makePlot(bytes_source, bytesPerIO)
        line, = tx.plot(xs, ys)
        line.set_label("MB/IO")
        cur =  ys[-1] if len(ys)>0 else 0
        tx.set_ylabel("MB/IO")
        tx.legend(loc="upper right")
        tx.set_ylim(bottom=0, top=cur*2)
    try:
        plotIORate(timeSeries.nextOpAxis(), "read")
        plotIORate(timeSeries.nextOpAxis(), "write")
    except: raise

    def plotCacheEstimates(ax):
        ax.set_title("data set size")
        def writeCountEstimate(t):
            #workload a
            assume_initialRecords = 1e6
            assume_writeFraction = 0.5
            return timeSeries.timeToOp(t)*assume_writeFraction + assume_initialRecords
        def dataSizeEstimate(t):
            assume_keySize = 24
            assume_valueSize = 512
            return writeCountEstimate(t) * (assume_keySize + assume_valueSize) / GB
        line, = ax.plot(*timeSeries.makePlot(e.ops_completed, dataSizeEstimate))
        line.set_label("data stored (GB)")
        ax.set_ylim(bottom=0)
        ax.legend()
    try:
        plotCacheEstimates(timeSeries.nextOpAxis())
    except: raise

    plotHelper.save("%s-perf.png" % e.filename)
    
plot_perf_timeseries(Experiment(sys.argv[1]))
