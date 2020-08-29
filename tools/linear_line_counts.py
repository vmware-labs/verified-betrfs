#!/usr/bin/env python3
"""
A hand-tuned script for doing head-to-head line counts of linear component across branches.
"""

import json
import collections
import subprocess
import line_count_lib
import line_counter_report_lib

def do_cmd(cmd):
    print("CMD", " ".join(cmd))
    subprocess.call(cmd)

class Package:
    def __init__(self, label, branch, sources):
        self.label = label
        self.branch = branch
        self.sources = sources
        self.counter = collections.Counter()

    def count(self):
        do_cmd(["git", "checkout", self.branch])
        print("NOW ON", cur_branch())
        for source in self.sources:
            self.count_one(source)

    def count_one(self, source):
        counter = line_count_lib.Counter(".")
        dafnyFile = line_count_lib.DafnyFile(source, 0.0)
        counter.collect_line_counts([dafnyFile])
        self.counter["spec"] += dafnyFile.spec
        self.counter["impl"] += dafnyFile.impl
        self.counter["proof"] += dafnyFile.proof
        self.display("intermediate")

    def display(self, msg):
        print(msg, self.label, self.counter)

    def jsondict(self):
        d = dict(self.counter)
        d["label"] = self.label
        d["branch"] = self.branch
        d["sources"] = self.sources
        return d

packages = [
    Package("Hashtable-linear", branch="eval-btree-linear", sources=
            ["lib/DataStructures/LinearMutableMap.i.dfy"]),
    Package("Hashtable-master", branch="eval-btree-master", sources=
            ["lib/DataStructures/MutableMapModel.i.dfy",
                "lib/DataStructures/MutableMapImpl.i.dfy"]),
    Package("BTree-linear", branch="eval-btree-linear", sources=
            ["lib/DataStructures/BtreeModel.i.dfy",
                "lib/DataStructures/MutableBtree.i.dfy"]),
    Package("BTree-master", branch="eval-btree-master", sources=
            ["lib/DataStructures/BtreeModel.i.dfy",
                "lib/DataStructures/MutableBtree.i.dfy"]),
    ]

def cur_branch():
    return subprocess.run("git rev-parse --abbrev-ref HEAD".split(), stdout=subprocess.PIPE).stdout.decode("utf-8").strip()

DATA_FILE = "data/linear_lines.json"
def collect():
    start_branch = cur_branch()

    try:
        accum = []
        for package in packages:
            package.count()
            accum.append(package.jsondict())
        open(DATA_FILE, "w").write(json.dumps(accum, indent=2))
    finally:
        do_cmd(["git", "checkout", start_branch])

# Translation table from package labels to tex macro names & table labels.
tex_names = {
        "Hashtable-linear": {"macroPrefix": "HashtableLinear", "tableModule": "Hashtable", "tableMode": "linear"},
        "Hashtable-master": {"macroPrefix": "HashtableRepr", "tableModule": "Hashtable", "tableMode": "dyn. frames"},
        "BTree-linear": {"macroPrefix": "BTreeLinear", "tableModule": "BTree", "tableMode": "linear"},
        "BTree-master": {"macroPrefix": "BTreeRepr", "tableModule": "BTree", "tableMode": "dyn. frames"},
        }

def report():
    data = json.loads(open(DATA_FILE).read())
    fp = open("../veripapers/osdi2020/data/linear-line-counts.tex", "w")
    for row in data:
        tex = tex_names[row["label"]]
        macroPrefix = tex["macroPrefix"]
        fp.write("\\newcommand{\\%sImpl}{%d}\n" % (macroPrefix, row["impl"]))
        fp.write("\\newcommand{\\%sProof}{%d}\n" % (macroPrefix, row["proof"]))
        fp.write("\\newcommand{\\%sRatio}{%.1f$\\times$}\n" % (macroPrefix, (1.0*row["proof"]/row["impl"])))
    fp.close()

    fp = open("../veripapers/osdi2020/data/linear-line-count-table.tex", "w")
    fp.write("\\begin{tabular}{|ll|rrr|}\n")
    fp.write("\\\\ \\hline\n")
    fp.write("component & style & impl. & proof & ratio \\\\\n")
    fp.write("\\\\ \\hline\n")
    for row in data:
        tex = tex_names[row["label"]]
        macroPrefix = tex["macroPrefix"]
        fp.write("%s & %s & \\%sImpl & \\%sProof & \\%sRatio \\\\\n" %
            (tex["tableModule"], tex["tableMode"], macroPrefix, macroPrefix, macroPrefix))
    fp.write("\\\\ \\hline\n")
    fp.write("\\end{tabular}\n")
    fp.close()

def main():
    #collect()
    report()
        
main()
