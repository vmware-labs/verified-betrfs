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

def plot_perf_compare(experiments):
    plotHelper = PlotHelper(3)

    for e in experiments:
        e.nickname = e.filename.split("/")[-1]

    def plotThroughput(ax):
        ax.set_title("op throughput")
        for e in experiments:
            nick = e.filename.split("/")[-1]
            timeSeries = TimeSeries(e, plotHelper)
            timeSeries.smoothedThroughput(ax, 10, label=e.nickname)
            timeSeries.smoothedThroughput(ax, 100, linestyle="dotted")

        ax.set_ylim(bottom = 0)
        ax.set_ylabel("Kops/sec")
        ax.set_xlabel("op num (K)")
        ax.legend()

    ax = plotHelper.nextAxis()
    try: plotThroughput(ax)
    except: raise

    def safeMap(xs, lam):
        outxs = []
        ys = []
        for x in xs:
            try:
                y = lam(x)
                outxs.append(x)
                ys.append(y)
            except:
                pass
        return outxs,ys
    def plotRateBargraph(ax, at_kopn):
        ax.set_title("mean opn rate after %d kops" % at_kopn)
        for exp in experiments:
            print("%s: %s" % (exp.nickname, TimeSeries(exp, plotHelper).kop_end))
        rows = range(len(experiments))
        rowlabels = [experiments[row].nickname for row in rows]
        def rateFor(exp):
            ts = TimeSeries(exp, plotHelper)
            at_opn = at_kopn*Kilo
            at_t = ts.opToTime(at_opn)
            #print(exp.nickname, at_t, at_opn)
            return at_opn/at_t
        #widths = [rateFor(experiments[row]) for row in rows]
        rows, widths = safeMap(rows, lambda row: rateFor(experiments[row])/Kilo)
        ax.set_yticks(rows)
        ax.set_yticklabels([rowlabels[row] for row in rows])
        ax.barh(rows, widths, align="center")
        ax.set_xlabel("op rate Kops/sec")
        #print("rows", rows, "widths", widths)
        for rowi in range(len(rows)):
            #print(row, widths[row])
            row = rows[rowi]
            ax.text(widths[rowi], row, "%.1f" % widths[rowi])
    plotRateBargraph(plotHelper.nextAxis(), 10000)
    plotRateBargraph(plotHelper.nextAxis(), 17000)

    plotHelper.save("compare.png")

experiments = [Experiment(fn) for fn in sys.argv[1:]]
plot_perf_compare(experiments)
