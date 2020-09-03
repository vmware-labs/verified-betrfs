#!/usr/bin/env python3

import re
import math
import numpy as np
import matplotlib.pyplot as plt
import glob
import collections
import tarfile

#EXPERIMENT="expresults/veri_time_13-*"
EXPERIMENT="build/verification-times.tgz"

class Observation:
    def __init__(self, time, worker_name, source_filename):
        self.time = time
        self.worker_name = worker_name
        self.source_filename = source_filename

    def __repr__(self):
        return "%s@%s" % (self.time, self.worker_name)

class SymbolReport:
    def __init__(self, name):
        self.name = name
        self.observations = []

    def add(self, obs):
        self.observations.append(obs)

    def times(self):
        return [obs.time for obs in self.observations]

    def avg(self):
        # called "avg" so I don't feel bad changing from mean to median
        return np.median(self.times())

    def stdev(self):
        return np.std(self.times())

    def cv(self):
        return self.stdev() / self.avg()

class SymbolPile:
    def __init__(self):
        self.symbols = {}
        self.avg_times_ = None

    def put_replica(self, name, obs):
        assert not self.avg_times_
        if name not in self.symbols:
            self.symbols[name] = SymbolReport(name)
        self.symbols[name].add(obs)

    def reports(self):
        return list(self.symbols.values())

    def avg_times(self):
        if self.avg_times_ == None:
            self.avg_times_ = [report.avg() for report in self.reports()]
            self.avg_times_.sort()
        return self.avg_times_ 

    def N(self):
        return len(self.avg_times())

    def cdist(self, i):
        return i*1.0/self.N()

def parse_one(opener, pile):
    symbol_parts = {}

    def record_part(symbol, part, obs):
        if symbol not in symbol_parts:
            symbol_parts[symbol] = []
        symbol_parts[symbol].append(obs)
        obs.part = part

    worker_name = None
    fn,fp = opener()
    for line in fp.readlines():
        if not type(line) == type(""):
            line = line.decode("utf-8")
        if line.startswith("Parsing"):
            source_filename = line.split()[-1]
        if line.startswith("WORKER"):
            worker_name = line.split()[-1]
        mo = re.compile("Verifying (\S*) \.\.\.").search(line)
        if mo!=None:
            part,symbol = mo.groups()[0].split("$$")
        mo = re.compile("\[([0-9\.]+) s,.*\]  verified").search(line)
        if mo!=None:
            time = float(mo.groups()[0])
            record_part(symbol, part, Observation(time, worker_name, source_filename))

    # now gather up the parts and put them in the statistics pile
    for symbol,observations in symbol_parts.items():
        # Take the max observation. If a method has a CheckWellFormed$$ and an
        # Impl$$, the Impl$$ is typically much longer. They can be dispatched
        # in parallel (/vcsCores), so the max is what describes user-experienced
        # delay.
        pile.put_replica(symbol, max(observations, key=lambda obs: obs.time))

def parse_all():
    pile = SymbolPile()
    openers = []
    if "*" in EXPERIMENT:
        # Load a glob out of the filesystem for interactive experimenting
        resultsfiles = glob.glob(EXPERIMENT)
        def opener(fn):
            return lambda: (fn,open(fn))
        openers = [opener(fn) for fn in resultsfiles]
    else:
        # Load from a tarball for git recorded raw data.
        tf = tarfile.open(EXPERIMENT, "r")
        resultsfiles = tf.getnames()
        def opener(fn):
            return lambda: (fn,tf.extractfile(fn))
        openers = [opener(fn) for fn in resultsfiles]
        
    if len(openers) == 0:
        raise Exception("No files match %s" % EXPERIMENT)
    for opener in openers:
        parse_one(opener, pile)
    return pile

def detect_bogus_workers(pile):
    """identify workers that consistently produce absurdly high results"""
    offending_workers = collections.Counter()
    for report in pile.reports():
        if report.cv() < 0.3: continue
        worst = max(report.observations, key=lambda obs: obs.time)
        offending_workers[worst.worker_name] += 1
    bogus_workers=set()
    for worker,count in offending_workers.items():
        if count>20:
            bogus_workers.add(worker)
        #print("bogus", worker, count)
    return bogus_workers

def reject_bogus_workers(pile, bogus_workers):
    """remove samples taken on bogus AWS worker nodes."""
    newpile = SymbolPile()
    for symbol,report in pile.symbols.items():
        for obs in report.observations:
            if obs.worker_name not in bogus_workers:
                newpile.put_replica(symbol, obs)
    return newpile

class Declaration:
    def __init__(self, line, decl_type):
        self.line = line
        self.decl_type = decl_type
        self.repr = set()

    def is_repr(self):
        return len(self.repr)>0

def parse_dfy_for_reprness(source_filename):
    table = {}
    current_symbol = None
    for line in open(source_filename).readlines():
        mo = re.compile("(method|lemma|function|predicate)[^\(]*\s(\S*)\(").search(line)
        if mo!=None:
            decl_type = mo.groups()[0]
            current_symbol = mo.groups()[1]
            table[current_symbol] = Declaration(line, decl_type)

        mo = re.compile("^\s*(modifies|reads)").search(line)
        if mo!=None:
            repr_verb = mo.groups()[0]
            table[current_symbol].repr.add(repr_verb)
    return table

def get_declaration(source_filename, symbol):
    needle = symbol.split(".")[-1]
    # hard-code some of these indirect refinement methods that I looked up by hand.
    # Each of these is a method that turns out to involve Reprs, but doesn't
    # modifies anything, so I assume there are no VCs related to it. ?
    if symbol in ("IndirectionTableImpl.IndirectionTable.indirectionTableToVal",
            "NodeImpl.Node.CutoffNodeAndKeepLeft",
            "DynamicPkv.__default.MergeToOneChild",
            "IndirectionTableImpl.IndirectionTable.ComputeRefCounts",
            ):
        notRepr = Declaration(None, "lemma")    # force a "sure false"
        return notRepr
    if symbol in ("KMBtree.__default.SplitChildOfIndex",):
        yesRepr = Declaration(None, "method")    # force a "sure true"
        yesRepr.repr.add("pseudo")
        return yesRepr
    try:
        return parse_dfy_for_reprness(source_filename)[needle]
    except KeyError:
        return None # refines from another file, probably

def report_slowest_symbols(pile):
    """report on slowest symbols. Are they dynamic-frames-repr disasters?"""

    bySlow = list(pile.reports())
    bySlow.sort(key=lambda r: -r.avg())
    for slowest in bySlow[:10]:
        print("slowest %s %.1fs" % (slowest.name, slowest.avg()))

def report_sequential_time(pile):
    print("Total sequential time: %.1fs" % sum(pile.avg_times()))

def emit_constants(defs):
    with open("../veripapers/osdi2020/data/verification-constants.tex", "w") as fp:
        fp.write("% generated by tools/automation-study.py\n")
        for k,v in defs.items():
            fp.write("\\newcommand{\\%s}{%s}\n" % (k, v))

class CdfPoint:
    def __init__(self, tex_label, thresh_sec, pile):
        self.tex_label = tex_label
        self.thresh_sec = thresh_sec

        idx,t = next((idx,t) for idx,t in enumerate(pile.avg_times()) if t>thresh_sec)
        self.idx = idx - 1

        self.tThr = pile.avg_times()[self.idx]
        self.yThr = pile.cdist(self.idx)
        self.pct = pile.cdist(self.idx)*100
        self.pct_text = "%.1f" % self.pct

        reports = pile.reports()
        reports.sort(key = lambda r: -r.avg())
        repr_set = set()
        no_repr_set = set()
        for r in reports:
            if r.avg()<=thresh_sec: break
            #print("slowest", r.name, r.avg())
            source_filename = r.observations[0].source_filename
            decl = get_declaration(source_filename, r.name)
            if decl and decl.is_repr():
                repr_set.add(r)
            elif decl and decl.decl_type == "lemma":
                no_repr_set.add(r)
            else:
                # not 100% sure; maybe refines method?
                no_repr_set.add(r)
                if thresh_sec==20:
                    print("unsure", r.name, r.avg(), source_filename)
        all_slow_count = len(repr_set)+len(no_repr_set)
        print("all_slow_count", all_slow_count)
        pct_slow = 100.0*len(repr_set)/all_slow_count
        self.defs = dict((self.tex_label + k,v) for k,v in {
            "SlowThresholdSecs": self.thresh_sec,
            "NumSlowVerifications": all_slow_count,
            "PctOfSlowVerifsInvolvingHeap": ("%d\\%%" % pct_slow),
            "FasterPctile": ("%s\\%%" % self.pct_text),
            }.items())

class CDFStuff:
    def __init__(self, pile):
        self.pile = pile
        self.ys = [pile.cdist(i) for i in range(pile.N())]

        self.point10s = CdfPoint("tenSec", 10, pile)
        self.point20s = CdfPoint("twentySec", 20, pile)

    def defs(self):
        defs = {}
        defs.update(self.point10s.defs)
        defs.update(self.point20s.defs)
        return defs

def plot_all(pile):
    cdf = CDFStuff(pile)
    def complog(y):
        return -math.log10(1-y)
    ys = [complog(y) for y in cdf.ys]

    fig = plt.figure(figsize=(6*0.8,2.5*0.8))
    ax = fig.add_subplot(111)
    ax.plot(cdf.pile.avg_times(), ys)

    for point in (cdf.point20s, cdf.point10s):
        ylogThr = complog(point.yThr)
        y0 = complog(0)
        ax.plot([0, point.tThr, point.tThr], [ylogThr, ylogThr, y0], color="gray")
        yOff = 0.80 if point==cdf.point10s else 0.99
        ax.text(point.tThr*1.01, ylogThr*yOff, va="top", s="%s%% faster than %ds" % (point.pct_text, point.thresh_sec))

    yticks = range(4)
    ax.set_yticks(yticks)
    ax.set_yticklabels([1-math.pow(10, -y) for y in yticks])
    ax.set_xlabel("time to verify definition, method or lemma (s)")
    ax.set_ylabel("cumulative frac.\n(log scale)")
    plt.tight_layout()

    fig.savefig("build/verification-times.pdf")

def main():
    pile = parse_all()
    bogus_workers = detect_bogus_workers(pile)
    print("Rejecting bogus workers: ", bogus_workers)
    pile = reject_bogus_workers(pile, bogus_workers)
    detect_bogus_workers(pile)
    report_slowest_symbols(pile)
    report_sequential_time(pile)
    #emit_constants(CDFStuff(pile).defs())
    plot_all(pile)

main()
