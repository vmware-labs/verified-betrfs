#!/usr/bin/python

import os
import re
import sys
import glob
from lib_deps import *

class InvalidDafnyIncludePath(Exception):
    def __init__(self, iref):
        self.iref = iref

    def msg(self):
        return "Includes must not contain ..; got %s" % (self.iref)

    def __str__(self):
        return self.msg()

class UndeclaredTrustedness(Exception):
    def __init__(self, iref):
        self.iref = iref

    def msg(self):
        return "Dafny file %s must declare trustedness with .s.dfy or .i.dfy extension" % self.iref

    def __str__(self):
        return self.msg()

class IncompatibleIncludeTrustedness(Exception):
    def __init__(self, iref, origin):
        self.iref = iref
        self.origin = origin

    def msg(self):
        return "Trusted .s files may only include other trusted .s files; %s includes %s" % (self.origin, self.iref)

    def __str__(self):
        return self.msg()

def targetName(iref, suffix):
    targetRootRelPath = iref.normPath.replace(".dfy", suffix)
    result = "$(BUILD_DIR)/%s" % targetRootRelPath
    return result

def deps(iref):
    return target(iref, ".deps")

BUILD_DIR = "build" # The build dir; make clean = rm -rf $BUILD_DIR
DIR_DEPS = "dir.deps"   # The per-directory dependencies file

def main():
    directory = IncludeReference(None, 0, sys.argv[1])
    dfyList = glob.glob(os.path.join(directory.absPath, "*.dfy"))
    targets = [IncludeReference(directory, i+1, dfyList[i]) for i in range(len(dfyList))]

    outputFilename = os.path.join(os.path.join(os.path.join(
        ROOT_PATH, BUILD_DIR), directory.normPath), DIR_DEPS)

    dirDeps = set()    # accumulate cross-directory refs
    fileDeps = []   # accumulate inter-file refs
    for target in targets:
        fileDeps.append("")
        fileDeps.append("# deps from %s" % target)
        allDeps = depsFromDfySource(target)
        for dep in allDeps[::-1]:
            for targetType in (".synchk", ".verchk", ".cs", ".cpp"):
                fileDeps.append("%s: %s" % (targetName(target, targetType), targetName(dep, targetType)))
            dirDeps.add(os.path.dirname(dep.normPath))
            fileDeps.append("%s: %s" % (targetName(target, ".verified"), targetName(dep, ".verchk")))
            fileDeps.append("%s: %s" % (targetName(target, ".verified"), targetName(dep, ".verified")))
        fileDeps.append("%s: %s" % (outputFilename, target.absPath))
    if (directory.normPath in dirDeps):
        dirDeps.remove(directory.normPath)

    outfp = open(outputFilename, "w")
    dirDeps = list(dirDeps)
    dirDeps.sort()
    for dirDep in dirDeps:
        outfp.write("include %s\n" % os.path.join("$(BUILD_DIR)", os.path.join(dirDep, DIR_DEPS)))
    for fileDep in fileDeps:
        outfp.write(fileDep + "\n")
    outfp.close()

if (__name__=="__main__"):
    main()
