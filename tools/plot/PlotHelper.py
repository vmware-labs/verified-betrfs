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
        if opnBefore < 0: return None
        num = num_trace[opn] - num_trace[opnBefore]
        denom = denom_trace[opn] - denom_trace[opnBefore]
        if denom == 0:
            return None
        rate = num/scale()/denom
        return rate
    return val

def singleTrace(ax, trace, scale=Unit):
    ax.set_ylabel("%s%s" % (scale, trace.units))
    return lambda opn: trace[opn]/scale()
