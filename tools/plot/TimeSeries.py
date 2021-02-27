# Copyright 2018-2021 VMware, Inc.
# SPDX-License-Identifier: MIT

from PlotHelper import *    # scale prefixes such as Kilo

Time = "time"
OpCount = "opCount"

class TimeSeries:
    def __init__(self, exp, plotHelper):
        self.exp = exp
        self.plotHelper = plotHelper

#        self.opValues = list(exp.ops_completed.values())
#        self.opValues.sort()
#        self.opTimes = list(exp.ops_completed.keys())
#        self.opTimes.sort()

#        self.t_end = max(self.exp.ops_completed.keys())
#        self.kop_end = self.timeToKiloOp(self.t_end)

    def nextOpAxis(self):
        ax = self.plotHelper.nextAxis()
        ax.set_xlim(left = 0, right=self.kop_end)
        return ax

    def timeToOp(self, t):
        idx = bisect.bisect(self.opTimes, t)
        if idx>=len(self.opTimes):
            idx = len(self.opTimes) - 1
        return self.opValues[idx]

    def opToTime(self, op):
        idx = bisect.bisect(self.opValues, op)
        return self.opTimes[idx]

    def timeToKiloOp(self, t):
        op = self.timeToOp(t)
        return op / Kilo

    def timesToKiloOps(self, ts):
        return [self.timeToKiloOp(t) for t in ts]

    def makePlot(self, xSource, lam):
        xs = []
        ys = []
        for t in xSource:
            try:
                x = self.timeToKiloOp(t)
                y = lam(t)
                if x!=None and y != None:
                    xs.append(x)
                    ys.append(y)
            except KeyError: pass
            except IndexError: pass
        assert None not in xs
        assert None not in ys
        return xs,ys

    def smooth(self, ax, window, source, fieldfunc, divideBy=Time, scale=1.0, label=None, linestyle=None, color=None):
        # window is in time units, not ops. Sorry.
        def valueAt(t):
            curOpn = self.timeToOp(t)
            prevOpn = self.timeToOp(t - window)
            numerator = fieldfunc(t) - fieldfunc(t-window)
            denominator = window if divideBy==Time else curOpn - prevOpn
            result = numerator/denominator/scale
            return result
        xs,ys = self.makePlot(source, valueAt)
        line, = ax.plot(xs, ys, linestyle=linestyle, color=color)
        if label:
            line.set_label(label)
        return ys[-1] if len(ys)>0 else 0

    def smoothedThroughput(self, ax, window, label=None, linestyle=None):
        return self.smooth(ax, window, source=self.exp.ops_completed, fieldfunc=lambda t: self.exp.ops_completed[t], divideBy=Time, scale=Kilo, label=label, linestyle=linestyle)

    def plotThroughput(self, ax):
        ax.set_title("op throughput")
        self.smoothedThroughput(ax, 10)
        cur = self.smoothedThroughput(ax, 100)
        ax.set_ylim(bottom = 0)
        ax.set_ylabel("Kops/sec")
        ax.set_xlabel("op num (K)")

        xs = [t for t in self.exp.ops_completed]
        def aggregateAt(time, label):
            if time > xs[-1]:
                return
            aggregate = (self.exp.ops_completed[time] - self.exp.ops_completed[xs[0]])/float(time)/Kilo
            msg = "mean %.1f" % aggregate
            if label == "end":
                msg += "\ncur %.2f" % cur
            ax.text(self.timeToKiloOp(time), aggregate, msg, horizontalalignment="right")
        aggregateAt(xs[-1], "end")
        t1m = self.opToTime(2000000)
        aggregateAt(t1m, "op1000k")
        
        axtwin = ax.twinx()
        ts = [t for t in self.exp.ops_completed]
        ops = [self.exp.ops_completed[t]/Kilo for t in xs]
        axtwin.plot(ops,ts, "g")
        axtwin.set_ylabel("time (s)")
