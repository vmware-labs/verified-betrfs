from PlotHelper import *    # scale prefixes such as Kilo

class TimeSeries:
    def __init__(self, exp, plotHelper):
        self.exp = exp
        self.plotHelper = plotHelper

        self.opValues = list(exp.ops_completed.values())
        self.opValues.sort()
        self.opTimes = list(exp.ops_completed.keys())
        self.opTimes.sort()

        self.t_end = max(self.exp.ops_completed.keys())
        self.kop_end = self.timeToKiloOp(self.t_end)

    def nextOpAxis(self):
        ax = self.plotHelper.nextAxis()
        ax.set_xlim(left = 0, right=self.kop_end)
        return ax

    def timeToOp(self, t):
        return self.exp.ops_completed[t]

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

    def smoothedThroughput(self, ax, window, label=None, linestyle=None):
        xs,ys = self.makePlot(self.exp.ops_completed, lambda t: (self.exp.ops_completed[t] - self.exp.ops_completed[t-window])/float(window)/Kilo)
        line, = ax.plot(xs, ys, linestyle=linestyle)
        if label:
            line.set_label(label)
        return ys[-1] if len(ys)>0 else 0

