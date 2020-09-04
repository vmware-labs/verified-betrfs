#!/usr/bin/env python3

import re
import json
import sys
from lib_deps import *
import matplotlib
import matplotlib.pyplot as plt

def relevantSources():
    dafnyRoot = "Impl/Bundle.i.dfy"
    return depsFromDfySources([dafnyRoot])

lineComment = re.compile(r'//.*$')
blockComment = re.compile(r'/[*]([^*]|[*]+[^/])*[*]+/')
startComment = re.compile(r'/[*].*$')
endComment = re.compile(r'^.*[*]/')
refToLine = {}
refToLines = {}

class LineReference(IncludeReference):
    """We want to hash file:line refs. IncludeReference is almost what we need,
    but its notion of identity is just the file; the line number is the
    referent, not the target."""
    def _tuple(self):
        return (self.absPath, self.line_num)

def grepOne(iref, regex):
    rec = re.compile(regex)
    if iref in refToLines:
        lines = refToLines[iref]
    else:
        lines = open(iref.normPath).readlines()
        lines = [lineComment.sub('', line) for line in lines] # remove // comments
        lines = [blockComment.sub('', line) for line in lines] # remove single-line /* */ comments
        lines = [startComment.sub('/*', line) for line in lines] # simplify multi-line /*
        lines = [endComment.sub('*/', line) for line in lines] # simplify multi-line */
        refToLines[iref] = lines
    output = set()
    inComment = False
    for i in range(len(lines)):
        line = lines[i]
        if line.startswith('*/'):
            inComment = False
        if not inComment and rec.search(line):
            ir = LineReference(iref, i+1, iref.absPath)
            output.add(ir)
            refToLine[ir] = line
        if line.strip().endswith('/*'):
            inComment = True
    return output

def grepAll(regex):
    instances = set()
    for filename in relevantSources():
        instances = instances.union(grepOne(filename, regex))
    return instances

def lineForIref(iref):
    return open(iref.normPath).readlines()[iref.line_num-1].strip()

def symbolNameForOpaqueIref(iref):
    line = lineForIref(iref)
    mo = re.compile("{:opaque}( |{[^}]*})*(\w+)[\(<]").search(line)
    if mo==None:
        print("XXX no match at ", line)
        return None
    return mo.groups()[1]

def opaqueInstances():
    opaqueRefs = grepAll("{:opaque}")
    records = []
    #print("%s refs" % len(opaqueRefs))
    for iref in opaqueRefs:
        symbolName = symbolNameForOpaqueIref(iref)
        #print(symbolName)
        reveal_lines = grepAll("reveal_%s\\b" % symbolName)
        reveal_count = len(reveal_lines)
        record = {"file": iref.normPath, "line": iref.line_num, "symbol":symbolName, "reveal_count":reveal_count}
        records.append(record)
        print("revealed %2d times: %s in %s at %s" % (reveal_count, symbolName, iref.normPath, iref.line_num))
        #sys.stdout.flush()
    return records

INTERMEDIATE = "build/auto.data"

def scrape():
    records = opaqueInstances()
    open(INTERMEDIATE, "w").write(json.dumps(records, indent = 4))

def plot(records):
    fig = plt.figure(figsize=(6*0.8,2.5*0.8))
    ax = fig.add_subplot(111)
    reveals = [record["reveal_count"] for record in records]
    reveals.sort()
    ax.hist(reveals, bins=max(reveals))
    ax.set_ylabel("count of\nopaque definitions")

    a2 = ax.twinx()
    xs = reveals
    ys = [i/(len(reveals)-1.0) for i in range(len(reveals))]
    a2.plot(xs, ys, color="red")
    a2.set_ylabel("cum. frac. of\nopaque definitions")
    ax.set_xlabel("number of times manually revealed")
    plt.tight_layout()
    fig.savefig("build/automation-figure.pdf")

def gather_constants(records):
    reveals = [record["reveal_count"] for record in records]
    reveals.sort()

    # print the top offenders
    records.sort(key=lambda r: r["reveal_count"])
    for record in records[-5:]:
        print(record)

    xs = reveals
    ys = [i/(len(reveals)-1.0) for i in range(len(reveals))]
    thresh5 = 5.0
    i5 = next((i for i,x in enumerate(xs) if x>thresh5))
    five_frac = ys[i5]

    return {
        "autoOpaqueCount": len(reveals),
        "autoRevealCount": sum(reveals),
        "autoRevealMean": "%.1f" % (sum(reveals)/len(reveals)),
        "autoRevealMax": max(reveals),
        "autoOpaqueZeroReveals": len([r for r in reveals if r==0]),
        "autoOpaqueFewReveals": len([r for r in reveals if r>0 and r<=3]),
        "autoFivePct": "%d\\%%" % (five_frac*100),
    }

def totalDefinitions(defs):
    defRef = grepAll("(function|predicate|method)")
    ghost = set()
    impl = set()
    all = set()
    for iref in defRef:
        line = lineForIref(iref)
        if "method" in line:
            impl.add(line)
        if "predicate" in line or "function" in line:
            ghost.add(line)
        all.add(line)
    allDefCount = len(all)
    defs.update({
        "autoAllDefnCount": allDefCount,
        "autoOpaquableDefnCount": len(ghost),
        "autoImplDefnCount": len(impl),
        "autoOpaquePct": "%d\\%%" % (100.0*defs["autoOpaqueCount"] / len(ghost)),
    })
    return defs

def find_dead_lemmas():
    lemmaRE = r'\blemma\b(\s|{[^}]+})+(?P<X>\w+)'
    lemmas = [re.search(lemmaRE, refToLine[r]).group('X') for r in grepAll(lemmaRE)]
    for x in lemmas:
        if len(grepAll(r"\b" + x + r"\b")) <= 1:
            print(x)

def main():
    scrape()

    records = json.loads(open(INTERMEDIATE).read())
    print("Got %s records" % len(records))
    plot(records)
    #defs = gather_constants(records)
    #defs = totalDefinitions(defs)
    #emit_constants(defs)

main()
