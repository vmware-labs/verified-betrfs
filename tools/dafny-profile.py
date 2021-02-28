# Copyright 2018-2021 VMware, Inc.
# SPDX-License-Identifier: BSD-2-Clause

import argparse
import os
import re
import subprocess
import sys
from termcolor import colored

parser = argparse.ArgumentParser('dafny-profile', epilog="""
This script runs Dafny on a file, profiling Z3's performance
on a particular Boogie procedure.  It reports the quantifiers
that are triggered most often.
""")

parser.add_argument("timelimit", help="Time limit for verification, in seconds")
parser.add_argument("proc", help="Boogie procedure to be verified, i.e., argument to /proc:")
parser.add_argument("filename", help="Dafny file name")
parser.add_argument("--metric", default="max", help="Sort by max count in profile output.",
                    choices=["max", "sum", "count"])
parser.add_argument("--dafny", help="Path for binary binary", default="./.dafny/dafny/Binaries/dafny")
parser.add_argument("--arg", help="Argument to be passed to Dafny", action='append')
parser.add_argument("--freq", help="Frequency to sample", default=1000)
parser.add_argument("--show", help="# number of profiler result shown", type=int, default=30)

class Profile:
    def __init__(self):
        self.by_max = {}
        self.by_sum = {}
        self.by_count = {}
    
    def parse(self, fn):
        ptrn = re.compile("\[quantifier_instances\] ([^ ]*) : *(\d+) :")
        for line in open(fn).readlines():
            line = line.strip()
            mo = ptrn.search(line)
            if mo != None:
                loc,count = mo.groups()
                count = int(count)
                self.by_max[loc] = max(self.by_max.get(loc, 0), count)
                self.by_sum[loc] = self.by_sum.get(loc, 0) + count
                self.by_count[loc] = self.by_count.get(loc, 0) + 1
                
    def display(self, d, label):
        tuples = list(d.items())
        tuples.sort(key=lambda i: (-i[1],i[0]))
        print("%10s %s" % (label, ""))
        for (loc,val) in tuples:
            if loc.startswith("DafnyPre") or loc.startswith("funType") or loc.startswith("unknown") or loc.startswith("cast:") or loc.startswith("typeInv"):
                color = "grey"
            else:
                color = "white"
            print("%10d %s" % (val, colored(loc, color)))

class Profiler:
    def __init__(self, args):
        self.args = args
        self.by_max = {}
        self.by_sum = {}
        self.by_count = {}
    
    def run_dafny(self):
        quantifier_pattern = re.compile("\[quantifier_instances\] ([^ ]*) : *(\d+) :")
        prover_error_pattern = re.compile("Prover error:")
        args = [self.args.dafny, "/timeLimit:" + self.args.timelimit, "/proc:" + str(self.args.proc),
                "/proverOpt:O:smt.qi.profile=true", "/proverOpt:O:smt.qi.profile_freq=" + str(self.args.freq)]
        if self.args.arg is not None:
            args.extend(self.args.arg)
        args.append(self.args.filename)

        print("Running command:")
        print(*args)
        print()

        proc = subprocess.Popen(args, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        for line in proc.stdout.readlines():
            line = line.decode().strip()
            mo = quantifier_pattern.search(line)
            if mo != None:
                loc,count = mo.groups()
                count = int(count)
                self.by_max[loc] = max(self.by_max.get(loc, 0), count)
                self.by_sum[loc] = self.by_sum.get(loc, 0) + count
                self.by_count[loc] = self.by_count.get(loc, 0) + 1
            if not prover_error_pattern.search(line) and len(line) > 0:
                print(line)
    
    def display(self, d, label):
        tuples = list(d.items())
        tuples.sort(key=lambda i: (-i[1],i[0]))

        if len(tuples) > self.args.show:
            tuples = tuples[0:self.args.show]

        print("%10s %s" % (label, ""))
        for (loc,val) in tuples:
            if loc.startswith("DafnyPre") or loc.startswith("funType") or loc.startswith("unknown") or loc.startswith("cast:") or loc.startswith("typeInv"):
                color = "grey"
            else:
                color = "white"
            print("%10d %s" % (val, colored(loc, color)))
    
    def run(self):
        self.run_dafny()
        source = {"max": self.by_max, "sum": self.by_sum, "count": self.by_count}
        self.display(source[args.metric], args.metric)

args = parser.parse_args()
profiler = Profiler(args)
profiler.run()
