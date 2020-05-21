#!/usr/bin/env python3
"""
A hand-tuned script for doing head-to-head line counts of linear component across branches.
"""

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

def main():
    start_branch = cur_branch()

    try:
        for package in packages:
            package.count()
            package.display("final")
    finally:
        do_cmd(["git", "checkout", start_branch])
        
main()
