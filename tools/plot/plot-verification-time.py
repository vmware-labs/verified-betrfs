#!/usr/bin/env python3

import re
import math
import numpy as np
import matplotlib.pyplot as plt
import glob
import collections
import tarfile

#EXPERIMENT="expresults/veri_time_13-*"
EXPERIMENT="expresults/veri_time_13.tgz"
SLOW_THRESH = 20

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

    def mean(self):
        return np.mean(self.times())

    def stdev(self):
        return np.std(self.times())

    def cv(self):
        return self.stdev() / self.mean()

class SymbolPile:
    def __init__(self):
        self.symbols = {}

    def put_replica(self, name, obs):
        if name not in self.symbols:
            self.symbols[name] = SymbolReport(name)
        self.symbols[name].add(obs)

    def reports(self):
        return list(self.symbols.values())

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

    reports = pile.reports()
    reports.sort(key = lambda r: -r.mean())
    repr_set = set()
    no_repr_set = set()
    for r in reports:
        if r.mean()<=SLOW_THRESH: break
        #print("slowest", r.name, r.mean())
        source_filename = r.observations[0].source_filename
        decl = get_declaration(source_filename, r.name)
        if decl and decl.is_repr():
            repr_set.add(r)
        elif decl and decl.decl_type == "lemma":
            no_repr_set.add(r)
        else:
            # not 100% sure; maybe refines method?
            no_repr_set.add(r)
            print("unsure", r.name, r.mean(), source_filename)
    all_slow_count = len(repr_set)+len(no_repr_set)
    print("all_slow_count", all_slow_count)
    pct_slow = 100.0*len(repr_set)/all_slow_count

    slowest = max(reports, key=lambda r: r.mean())
    print("slowest", slowest.name, slowest.mean())

    return {
        "slowThresholdSecs": SLOW_THRESH,
        "numSlowVerifications": all_slow_count,
        "pctOfSlowVerifsInvolvingHeap": ("%d\\%%" % pct_slow),
        }

def emit_constants(defs):
    with open("../veripapers/osdi2020/data/verification-constants.tex", "w") as fp:
        fp.write("% generated by tools/automation-study.py\n")
        for k,v in defs.items():
            fp.write("\\newcommand{\\%s}{%s}\n" % (k, v))

def plot_all(pile):
    mean_times = [report.mean() for report in pile.reports()]
    mean_times.sort()
    N = len(mean_times)
    def cdist(i):
        return i*1.0/N
    ys = [cdist(i) for i in range(N)]
    def complog(y):
        return -math.log10(1-y)
    ys = [complog(y) for y in ys]

    fig = plt.figure()
    ax = fig.add_subplot(111)
    ax.plot(mean_times, ys)

    idx,t = next((idx,t) for idx,t in enumerate(mean_times) if t>SLOW_THRESH)
    idx = idx - 1
    t = mean_times[idx]
    ypos = complog(cdist(idx))
    y0 = complog(0)
    ax.plot([0, t, t], [ypos, ypos, y0])
    ax.text(t*1.01, ypos*0.99, va="top", s="%.1f%% faster than %ds" % (cdist(idx)*100, SLOW_THRESH))

    yticks = range(4)
    ax.set_yticks(yticks)
    ax.set_yticklabels([1-math.pow(10, -y) for y in yticks])
    ax.set_xlabel("time to verify definition, method or lemma (s)")
    ax.set_ylabel("cumulative fraction (log scale)")

    fig.savefig("../veripapers/osdi2020/figures/verification-times.pdf")

def main():
    pile = parse_all()
    bogus_workers = detect_bogus_workers(pile)
    print("Rejecting bogus workers: ", bogus_workers)
    pile = reject_bogus_workers(pile, bogus_workers)
    detect_bogus_workers(pile)
    defs = report_slowest_symbols(pile)
    emit_constants(defs)
    plot_all(pile)

main()
