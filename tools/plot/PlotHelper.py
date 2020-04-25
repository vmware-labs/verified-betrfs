#!/usr/bin/env python3
import matplotlib
import matplotlib.pyplot as plt
from matplotlib.gridspec import GridSpec
import numpy as np
import sys
import operator
import bisect


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
    def __init__(self, numPlots, scale=1):
        self.numPlots = numPlots
        self.columns = 2 if numPlots > 4 else 1
        self.rows = int((numPlots+0.5)/self.columns)
        # You may need: sudo pip3 install --upgrade matplotlib
        self.fig = plt.figure(constrained_layout=True,
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
        plt.tight_layout()
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

def plotThroughput(ax, experiments):
    ax.set_title("op throughput")
    a2 = ax.twinx()
    a2.set_ylabel("s")
    colors = ["red", "blue", "purple"]
    xlim_right = 0
    for expi in range(len(experiments)):
        exp = experiments[expi]
        line, = ax.plot(*plotVsKop(ax, exp, windowedPair(ax, exp.operation, exp.elapsed, scale=K)), color=colors[expi])
        line.set_label(exp.nickname + " tput")
        ax.plot(*plotVsKop(ax, exp, windowedPair(ax, exp.operation, exp.elapsed, window=1000*K(), scale=K)), color=colors[expi], linestyle="dotted")

        def elapsedTime(opn):
            return exp.elapsed[opn]
        line, = a2.plot(*plotVsKop(ax, exp, elapsedTime), color=colors[expi])
        line.set_label(exp.nickname + " rate")

        xlim_right = max(xlim_right, exp.op_max/K())
    ax.set_xlim(left = 0, right=xlim_right)
    ax.legend(loc="upper center")
    ax.set_yscale("log")
    ax.set_ylim(bottom=0.1)
    ax.grid(which="major", color="black")
    ax.grid(which="minor", color="#dddddd")
    a2.legend(loc="lower center")
    
    for phase,opn in experiments[0].phase_starts.items():
        #print (phase,opn)
        ax.text(opn/K(), 0, phase)
