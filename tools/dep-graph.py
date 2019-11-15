#!/usr/bin/python3

import os
from lib_deps import *
from lib_aggregate import *

class Traverser:
    def __init__(self, rootDfy, outputFilename):
        self.output = []
        self.count = 0
        self.output.append("digraph {")

        self.visited = set()
        root = IncludeReference(None, 0, rootDfy)
        self.visit(root)

        self.addFillColors()

        # Ranks are too rigid; the whole of disk-betree gets rendered
        # in one wide row
        #self.addRanks()

        self.output.append("}")
        self.emit(outputFilename)

    def visit(self, iref):
        self.count += 1
        #print("visiting %d of %d" % (self.count, len(self.visited)))
        #print("as normpath: %d" % len(set([i.normPath for i in self.visited])))
        if iref in self.visited:
            return
        self.visited.add(iref)
        for dep in visit(iref):
            self.output.append('"%s" -> "%s";' % (iref.normPath, dep.normPath))
        for dep in visit(iref):
            self.visit(dep)

    def getSummary(self, iref):
        verchk = os.path.join(ROOT_PATH, "build", iref.normPath).replace(".dfy", ".verchk")
        return summarize(verchk)

    def addFillColors(self):
        for iref in self.visited:
            summary = self.getSummary(iref)
            self.output.append('"%s" [style=filled; color=%s; label="%s\n%ss"];' % (iref.normPath, summary.color, iref.normPath.replace("/", "/\n", 1), summary.userTimeSec))

    def sourceDir(self, iref):
        return iref.normPath.rsplit("/", 1)[0]

    def addRanks(self):
        prefixes = set([self.sourceDir(iref) for iref in self.visited])
        for prefix in prefixes:
            members = ['"%s"' % iref.normPath for iref in self.visited if self.sourceDir(iref) == prefix]
            self.output.append("{ rank=same; %s }" % (",".join(members)))

    def emit(self, outputFilename):
        fp = open(outputFilename, "w")
        for line in self.output:
            fp.write(line+"\n")
        fp.close()

rootDfy = sys.argv[1]
outputFilename = sys.argv[2]
Traverser(rootDfy, outputFilename)
