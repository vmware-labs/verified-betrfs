#!/usr/bin/python3
# Create the build/ directory, generate the initial build/makefile

import os
import re
import sys
import glob
from lib_deps import *

def targetName(iref, suffix):
    targetRootRelPath = iref.normPath.replace(".dfy", suffix)
    result = "build/%s" % targetRootRelPath
    return result

def deps(iref):
    return target(iref, ".deps")

BUILD_DIR = "build" # The build dir; make clean = rm -rf $BUILD_DIR
DIR_DEPS = "dir.deps"   # The per-directory dependencies file

class Veridepend:
    def __init__(self, dafnyRoots):
        self.dafnyRoots = dafnyRoots
        self.discoverAllDfys(self.dafnyRoots)
        output = self.gatherDeps()
        self.writeDepsFile(output)
        self.graph = {}

    def discoverAllDfys(self, dafnyRoots):
        irefs = set()
        for i in range(len(dafnyRoots)):
            dafnyRoot = dafnyRoots[i]
            rootIref = IncludeReference(None, i, dafnyRoot)
            irefs.add(rootIref)
            targets = depsFromDfySource(rootIref)
            irefs = irefs.union(set(targets))
        self.targetIrefs = irefs

    def gatherDeps(self):
        output = []
        for iref in toposortGroup(self.targetIrefs):
            output += self.generateDepsForIref(iref)
        return output

    def generateDepsForIref(self, iref):
        output = []
        output.append("")
        output.append("# deps from %s" % iref)
        for dep in childrenForIref(iref):
            for fromType,toType in (
                    # dummy dependencies to ensure that any targets depending
                    # on a dfy also get rebuilt when any upstream dfys change.
                    (".dummydep", ".dummydep"),
                    # depend on all included dfys by synchking each first.
                    (".synchk", ".dummydep"),
                    # depend on all included dfys, but don't require verifying
                    # all prior .cs files.
                    (".verchk", ".dummydep"),
                    # depend on all included dfys, but don't require building
                    # all prior .cs files.
                    (".cs", ".dummydep"),
                    # For now, depend on all prior .cpps, to make development
                    # of cpp backend easier.
                    (".cpp", ".cpp"),
                    # Verifieds are recursive to make top-level target depend
                    # on all the others.
                    (".verified", ".verified"),
                    # Corresponding recursive tree for synchk.
                    (".syntax", ".syntax"),

                    # When we build X.o, we first want to build Y.cpp and Y.o.
                    # These aren't true dependencies, but they make the ordering
                    # more convenient.
                    (".o", ".o"),
                    (".cpp", ".o"),
                    ):
                output.append("%s: %s" % (targetName(iref, fromType), targetName(dep, toType)))

            # dependencies from this file to type parents
            output.append("%s: %s" % (targetName(iref, ".verified"), targetName(dep, ".verchk")))
            output.append("%s: %s" % (targetName(iref, ".syntax"), targetName(dep, ".synchk")))
        # The dirDeps file depends on each target it describes.
        output.append("%s: %s" % (self.depFilename(), iref.normPath))
        return output

    def depFilename(self):
        return "build/deps"

    def writeDepsFile(self, outputLines):
        outfp = open(self.depFilename(), "w")
        for line in outputLines:
            outfp.write(line + "\n")
        outfp.close()

if (__name__=="__main__"):
    Veridepend(sys.argv[1:])
