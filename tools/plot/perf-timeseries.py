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

    plotHelper = PlotHelper(8)
    #timeSeries = TimeSeries(exp, plotHelper)

    def plotVsKop(ax, lam):
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
            except KeyError: pass
            except IndexError: pass
        assert None not in xs
        assert None not in ys
        return xs,ys

    def windowedPair(ax, num_trace, denom_trace, scale=Unit, window=100*K()):
        ax.set_ylabel("%s%s/%s" % (scale, num_trace.units, denom_trace.units))
        def val(opn):
            opnBefore = opn - window
            if opnBefore < 0: return None
            num = num_trace[opn] - num_trace[opnBefore]
            denom = denom_trace[opn] - denom_trace[opnBefore]
            if denom == 0:
                return None
            rate = num/scale()/denom
            return rate
        return val

    def singleTrace(ax, trace, scale=Unit):
        ax.set_ylabel("%s%s/Kop" % (scale, trace.units))
        return lambda opn: trace[opn]/scale()


    def plotThroughput(ax):
        ax.set_title("op throughput")
        #ax.set_ylabel("Kops/sec")
        line, = ax.plot(*plotVsKop(ax, windowedPair(ax, exp.operation, exp.elapsed, scale=K)))
        ax.plot(*plotVsKop(ax, windowedPair(ax, exp.operation, exp.elapsed, window=1000*K(), scale=K)))
        line.set_label("tput")
        ax.legend(loc="lower left")
        
        for phase,opn in exp.phase_starts.items():
            #print (phase,opn)
            ax.text(opn/K(), 0, phase)

        a2 = ax.twinx()
        def elapsedTime(opn):
            return exp.elapsed[opn]
        line, = a2.plot(*plotVsKop(ax, elapsedTime), color="green")
        line.set_label("elapsed")
        a2.set_ylabel("s")
        a2.legend(loc="center right")

    try:
        plotThroughput(plotHelper.nextAxis())
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
        line, = ax.plot(*plotVsKop(ax, windowedPair(ax, iomode.count_source, exp.operation, scale=Unit)), "red")
        line.set_label(iomode.label)
        ax.legend()

        a2 = ax.twinx()
        xs,ys = plotVsKop(a2, windowedPair(a2, iomode.byte_source, iomode.count_source, scale=Mi))
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
        line, = ax.plot(*plotVsKop(ax, windowedPair(ax, iomode.count_source, exp.elapsed, scale=Unit)), "red")
        line.set_label(iomode.label)
        ax.legend()

        a2 = ax.twinx()
        line, = a2.plot(*plotVsKop(a2, windowedPair(a2, iomode.byte_source, exp.elapsed, scale=Mi)))
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
        line, = ax.plot(*plotVsKop(ax, dataSizeEstimate))
        line.set_label("data stored")
        ax.set_ylabel("%sB" % scale)
        ax.set_ylim(bottom=0)
        ax.legend()
    try:
        plotCacheEstimates(plotHelper.nextAxis())
    except: raise

    class LambdaTrace:
        def __init__(self, lam, units):
            self.lam = lam
            self.units = units

        def __getitem__(self, opn):
            return self.lam(opn)

    def plotMemory(ax):
        ax.plot(*plotVsKop(ax, singleTrace(ax, exp.os_map_total, scale=Gi)))
    plotMemory(plotHelper.nextAxis())

    def plotCpuTime(ax):
        ticksPerSecond = os.sysconf(os.sysconf_names['SC_CLK_TCK'])
        user_sec = LambdaTrace(lambda opn: exp.utime[opn]/ticksPerSecond, "s")
        sys_sec = LambdaTrace(lambda opn: exp.stime[opn]/ticksPerSecond, "s")

        print("ticksPerSecond", ticksPerSecond)
        line, = ax.plot(*plotVsKop(ax, windowedPair(ax, user_sec, exp.elapsed)))
        line.set_label("user")
        line, = ax.plot(*plotVsKop(ax, windowedPair(ax, sys_sec, exp.elapsed)))
        line.set_label("sys")
        ax.legend()
    plotCpuTime(plotHelper.nextAxis())

    plotHelper.save("%s-perf.png" % exp.filename)
    
plot_perf_timeseries(Experiment(sys.argv[1]))
