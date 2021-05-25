#!/usr/bin/env python3

# Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
# SPDX-License-Identifier: BSD-2-Clause

# Args: dep-graph <synchk|verchk> root.dfy output.dot
# Gather the syntax or verification check output for all dfy files reachable
# from root.dfy. Construct a GraphViz dot file as output.

import os
import sys
from lib_deps import *
from lib_aggregate import *

class Traverser:
    def __init__(self, reportType, rootDfy, outputFilename):
        self.reportType = reportType
        self.output = {}
        for cond in allConditions:
            self.output[cond.result] = [];
        self.count = 0

        self.visited = set()
        root = IncludeReference(None, 0, rootDfy)
        self.visit(root)

        self.gatherResults()

        self.emit(outputFilename)

    def visit(self, iref):
        self.count += 1
        #print("visiting %d of %d" % (self.count, len(self.visited)))
        #print("as normpath: %d" % len(set([i.normPath for i in self.visited])))
        if iref in self.visited:
            return
        self.visited.add(iref)
        for dep in childrenForIref(iref):
            self.visit(dep)

    def getSummary(self, iref):
        report = os.path.join(ROOT_PATH, "build", iref.normPath).replace(".dfy", "."+self.reportType)
        return summarize(self.reportType, report)

    def gatherResults(self):
        for iref in self.visited:
            summary = self.getSummary(iref)
            self.output[summary.result].append(iref)

    def emit(self, outputFilename):
        fp = open(outputFilename, "w")
        hasErrors = False
        for cond in badConditions:
            if self.output[cond.result] != []:
                fp.write(cond.result + ":\n");
                hasErrors = True
            for iref in self.output[cond.result]:
                fp.write("  " + iref.normPath+"\n")
        if hasErrors == False:
            fp.write("No errors!\n")
        fp.close()

def main():
    try:
        reportType = sys.argv[1]
        assert reportType in ("verchk", "synchk")
        rootDfy = sys.argv[2]
        outputFilename = sys.argv[3]
    except:
        sys.stderr.write("usage: %s <verchk|synchk> root.dfy output.txt\n" % sys.argv[0])
        sys.exit(-1)
    Traverser(reportType, rootDfy, outputFilename)

main()
